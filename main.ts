import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const DIRS: [number, number, string, string][] = [[0, -1, 'u', 'U'], [0, 1, 'd', 'D'], [-1, 0, 'l', 'L'], [1, 0, 'r', 'R']];

type Level = { w: number, h: number, wall: Uint8Array, goals: number[], boxes: number[], player: number };
type Room = { squares: number[], boxes: number[], goals: number[], done?: boolean };

function parseLevel(text: string): Level {
  const rows = text.split('\n').filter((r) => r.length > 0);
  const h = rows.length, w = Math.max(...rows.map((r) => r.length));
  const wall = new Uint8Array(w * h).fill(1), goals: number[] = [], boxes: number[] = [];
  let player = -1;
  rows.forEach((row, y) => { for (let x = 0; x < row.length; x++) {
    const ch = row[x], i = y * w + x; if (ch === '#') continue; wall[i] = 0;
    if (ch === '.' || ch === '*' || ch === '+') goals.push(i);
    if (ch === '$' || ch === '*') boxes.push(i);
    if (ch === '@' || ch === '+') player = i;
  }});
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) if (x === 0 || y === 0 || x === w - 1 || y === h - 1) wall[y * w + x] = 1;
  boxes.sort((a, b) => a - b); goals.sort((a, b) => a - b);
  return { w, h, wall, goals, boxes, player };
}

function liveSquares(level: Level): Uint8Array {
  const { w, wall, goals } = level, live = new Uint8Array(wall.length), queue = goals.slice();
  for (const g of goals) live[g] = 1;
  for (let head = 0; head < queue.length; head++) { const x = queue[head]!;
    for (const [dx, dy] of DIRS) { const d = dy * w + dx, y = x - d;
      if (!wall[y] && !wall[y - d] && !live[y]) { live[y] = 1; queue.push(y); }
    }
  }
  return live;
}

function reach(level: Level, occupied: Uint8Array, from: number, seen: Int32Array, stamp: number, stack: Int32Array): number {
  const { w, wall } = level; let low = from, n = 0; stack[n++] = from; seen[from] = stamp;
  while (n > 0) { const p = stack[--n]!; if (p < low) low = p;
    for (let k = 0; k < 4; k++) { const q = k === 0 ? p - w : k === 1 ? p + w : k === 2 ? p - 1 : p + 1;
      if (wall[q] === 0 && occupied[q] === 0 && seen[q] !== stamp) { seen[q] = stamp; stack[n++] = q; }
    }
  }
  return low;
}

function frozenBlock(level: Level, occupied: Uint8Array, goal: Uint8Array, t: number): boolean {
  const { w, wall } = level;
  for (const a of [t, t - 1, t - w, t - w - 1]) { const b = a + 1, c = a + w, d = c + 1;
    if (!(wall[a] || occupied[a]) || !(wall[b] || occupied[b]) || !(wall[c] || occupied[c]) || !(wall[d] || occupied[d])) continue;
    if ((occupied[a] && !goal[a]) || (occupied[b] && !goal[b]) || (occupied[c] && !goal[c]) || (occupied[d] && !goal[d])) return true;
  }
  return false;
}

function keyOf(boxes: number[], low: number, size: number): string { return `${low}|${boxes.join(',')}`; }

function walkTo(level: Level, occupied: Uint8Array, from: number, to: number): string {
  if (from === to) return '';
  const { w, wall } = level, prev = new Int32Array(wall.length).fill(-1), how: string[] = [], queue = [from];
  prev[from] = from;
  for (let qi = 0; qi < queue.length; qi++) { const p = queue[qi]!; if (p === to) break;
    for (const [dx, dy, letter] of DIRS) { const q = p + dy * w + dx;
      if (wall[q] || occupied[q] || prev[q] !== -1) continue; prev[q] = p; how[q] = letter; queue.push(q);
    }
  }
  if (prev[to] === -1) throw new Error('unreachable push square');
  let out = ''; for (let p = to; p !== from; p = prev[p]!) out = how[p] + out; return out;
}

function solvePush(level: Level, maxStates = 500000): { pushes: number, moves: string } | null {
  const { w, wall, goals } = level, size = wall.length, goal = new Uint8Array(size), live = liveSquares(level);
  for (const g of goals) goal[g] = 1;
  if (level.boxes.some((b) => !live[b])) return null;
  const occupied = new Uint8Array(size), seen = new Int32Array(size), mark = new Int32Array(size), stack = new Int32Array(size);
  const statesBoxes: number[][] = [level.boxes.slice()], statesPlayer = [level.player], parent = [-1], index = new Map<string, number>();
  let stamp = 0; for (const b of level.boxes) occupied[b] = 1;
  index.set(keyOf(level.boxes, reach(level, occupied, level.player, seen, ++stamp, stack), size), 0);
  for (const b of level.boxes) occupied[b] = 0;
  let found = level.boxes.every((b) => goal[b]) ? 0 : -1;
  for (let head = 0; found < 0 && head < statesBoxes.length; head++) {
    const boxes = statesBoxes[head]!; for (const b of boxes) occupied[b] = 1;
    reach(level, occupied, statesPlayer[head]!, seen, ++stamp, stack); const here = stamp;
    for (let bi = 0; bi < boxes.length && found < 0; bi++) { const b = boxes[bi]!;
      for (const [dx, dy] of DIRS) { const d = dy * w + dx, t = b + d;
        if (seen[b - d] !== here || wall[t] || occupied[t] || !live[t]) continue;
        occupied[b] = 0; occupied[t] = 1; const frozen = frozenBlock(level, occupied, goal, t);
        let next: number[] | null = null, k = '';
        if (!frozen) { next = boxes.slice(); next[bi] = t; next.sort((a, c) => a - c); k = keyOf(next, reach(level, occupied, b, mark, ++stamp, stack), size); }
        occupied[t] = 0; occupied[b] = 1; if (frozen || index.has(k)) continue;
        if (statesBoxes.length >= maxStates) { for (const x of boxes) occupied[x] = 0; return null; }
        index.set(k, statesBoxes.length); statesBoxes.push(next!); statesPlayer.push(b); parent.push(head);
        if (next!.every((x) => goal[x])) { found = statesBoxes.length - 1; break; }
      }
    }
    for (const x of boxes) occupied[x] = 0;
  }
  if (found < 0) return null;
  const path: number[] = []; for (let s = found; s > 0; s = parent[s]!) path.push(s); path.reverse();
  let moves = '', player = level.player, boxes = level.boxes.slice();
  for (const s of path) { const next = statesBoxes[s]!, from = boxes.find((b) => !next.includes(b))!, to = next.find((b) => !boxes.includes(b))!, d = to - from;
    for (const b of boxes) occupied[b] = 1; moves += walkTo(level, occupied, player, from - d); for (const b of boxes) occupied[b] = 0;
    const dir = DIRS.find((entry) => entry[1] * w + entry[0] === d)!; moves += dir[3]; player = from; boxes = next;
  }
  return { pushes: path.length, moves };
}

function roomsOf(level: Level): Room[] | null {
  const { w, wall, goals, boxes, player } = level, live = liveSquares(level), row = Math.floor(player / w), cut = new Uint8Array(wall.length);
  for (let i = row * w; i < (row + 1) * w; i++) if (!wall[i] && !live[i]) cut[i] = 1;
  if (boxes.some((b) => cut[b])) return null;
  const part = new Int32Array(wall.length).fill(-1), rooms: Room[] = [];
  for (let s = 0; s < wall.length; s++) { if (wall[s] || cut[s] || part[s] >= 0) continue; const squares = [s]; part[s] = rooms.length;
    for (let i = 0; i < squares.length; i++) for (const [dx, dy] of DIRS) { const q = squares[i]! + dy * w + dx;
      if (!wall[q] && !cut[q] && part[q] < 0) { part[q] = rooms.length; squares.push(q); }
    }
    rooms.push({ squares, boxes: [], goals: [] });
  }
  for (const b of boxes) if (part[b] >= 0) rooms[part[b]]!.boxes.push(b);
  for (const g of goals) if (part[g] >= 0) rooms[part[g]]!.goals.push(g);
  if (goals.some((g) => part[g] < 0) || rooms.some((r) => r.boxes.length !== r.goals.length)) return null;
  return rooms.filter((r) => r.boxes.length > 0).sort((a, b) => Math.min(...a.boxes) - Math.min(...b.boxes));
}

function endOf(w: number, from: number, moves: string): number { let p = from; for (const ch of moves.toLowerCase()) p += ch === 'u' ? -w : ch === 'd' ? w : ch === 'l' ? -1 : 1; return p; }

function solve(level: Level): string {
  const rooms = roomsOf(level); if (!rooms) return solvePush(level)?.moves ?? '';
  let player = level.player, moves = '';
  for (const room of rooms) {
    const wall = level.wall.slice(); for (const other of rooms) if (other !== room) for (const b of other.done ? other.goals : other.boxes) wall[b] = 1;
    const sub: Level = { w: level.w, h: level.h, wall, goals: room.goals.slice().sort((a, b) => a - b), boxes: room.boxes.slice().sort((a, b) => a - b), player };
    const result = solvePush(sub); if (!result) return '';
    moves += result.moves; player = endOf(level.w, player, result.moves); room.done = true;
  }
  return moves;
}

for (const id of readdirSync(I).sort()) { const moves = solve(parseLevel(readFileSync(join(I, id, 'level.txt'), 'utf8'))); mkdirSync(join(O, id), { recursive: true }); writeFileSync(join(O, id, 'solution.txt'), `${moves}\n`); }
