"""Exploration only (not a proof dependency).

Find entry-certificate parameters for single black cells that the blank orbit visits early.
Every parameter printed here is re-verified by the Lean kernel (`checkSingleBlack`); nothing
from this script is trusted.

Conventions mirror LangtonsAnt.lean: white turns right, black turns left, flip, then move.
"""
import json
import sys

DIRS = ["north", "east", "south", "west"]
DELTA = {"north": (0, 1), "east": (1, 0), "south": (0, -1), "west": (-1, 0)}
RIGHT = {"north": "east", "east": "south", "south": "west", "west": "north"}
LEFT = {"north": "west", "east": "north", "south": "east", "west": "south"}
INV = {"north": "north", "east": "west", "south": "south", "west": "east"}

SEED = [(-2, -1), (2, -2), (2, -3), (2, -4), (2, -6), (1, -1),
        (-1, -4), (3, -5), (1, -5), (0, -3), (0, -2), (1, -3), (4, -4),
        (1, -4), (-1, 0), (0, -5), (0, -1), (0, 0), (-1, 1), (-2, 0),
        (2, -5), (1, -6), (-1, -3)]
SEED_SET = set(SEED)


def rot(r, p):
    x, y = p
    if r == "north":
        return (x, y)
    if r == "east":
        return (y, -x)
    if r == "south":
        return (-x, -y)
    return (-y, x)


def run_reads(black, pos, d, n):
    black = set(black)
    reads = []
    for _ in range(n):
        c = pos in black
        reads.append(c)
        d = LEFT[d] if c else RIGHT[d]
        if c:
            black.discard(pos)
        else:
            black.add(pos)
        pos = (pos[0] + DELTA[d][0], pos[1] + DELTA[d][1])
    return reads


STD = run_reads(SEED, (0, 0), "north", 104)


def entry_ok(black, pos, d):
    """EntryAt s 0 d pos: normalized board agrees with the seed on weight <= 0."""
    inv = INV[d]
    for b in black:
        q = rot(inv, (b[0] - pos[0], b[1] - pos[1]))
        if q[0] + q[1] <= 0 and q not in SEED_SET:
            return False
    for s in SEED:
        # seed cell s (normalized) must be black in the state
        b = rot(d, s)
        b = (b[0] + pos[0], b[1] + pos[1])
        if b not in black:
            return False
    return True


def find_entry(q, limit):
    black = {q}
    pos, d = (0, 0), "north"
    reads = []
    path = []
    checked_from = None
    t = 0
    while t <= limit:
        # candidate entry at time t: reads from t must equal STD; test lazily once
        # the last 3*104 reads are periodic
        if t >= 312 and t % 8 == 0 and checked_from is None:
            if reads[-104:] == reads[-208:-104] == reads[-312:-208]:
                checked_from = t
        if checked_from is not None and pos in black:
            # entry must begin at a phase where the next reads follow STD from 0;
            # verify exactly with the half-plane check
            if entry_ok(black, pos, d):
                return t, pos, d, path
        path.append(pos)
        c = pos in black
        reads.append(c)
        d = LEFT[d] if c else RIGHT[d]
        if c:
            black.discard(pos)
        else:
            black.add(pos)
        pos = (pos[0] + DELTA[d][0], pos[1] + DELTA[d][1])
        t += 1
    return None


def blank_early_cells(T0):
    black = set()
    pos, d = (0, 0), "north"
    first = {}
    for t in range(T0):
        if pos not in first:
            first[pos] = t
        c = pos in black
        d = LEFT[d] if c else RIGHT[d]
        if c:
            black.discard(pos)
        else:
            black.add(pos)
        pos = (pos[0] + DELTA[d][0], pos[1] + DELTA[d][1])
    return first


def main():
    T0 = int(sys.argv[1])
    limit = int(sys.argv[2])
    out = sys.argv[3]
    first = blank_early_cells(T0)
    cells = sorted(first, key=lambda p: first[p])
    print(f"early cells: {len(cells)}", flush=True)
    results = []
    total = 0
    for i, q in enumerate(cells):
        r = find_entry(q, limit)
        if r is None:
            results.append({"q": q, "fail": True})
            print(f"FAIL {q}", flush=True)
            continue
        T, P, d, path = r
        inv = INV[d]
        pts = [rot(inv, p) for p in path + [q, P]]
        xs = [p[0] for p in pts]
        ys = [p[1] for p in pts]
        cx = -((min(xs) + max(xs)) // 2)
        cy = -((min(ys) + max(ys)) // 2)
        span = max(max(xs) - min(xs), max(ys) - min(ys))
        # frame: G = rotate(inv d)(translate w X); need rotate(inv d)(w) = (cx, cy)
        w = rot(d, (cx, cy))
        o = rot(inv, (P[0] + w[0], P[1] + w[1]))
        results.append({"q": q, "T": T, "dir": d, "w": w, "o": o, "span": span,
                        "first": first[q]})
        total += T
        if (i + 1) % 100 == 0:
            print(f"{i+1}/{len(cells)} total steps {total}", flush=True)
    with open(out, "w") as f:
        json.dump(results, f)
    spans = [r["span"] for r in results if not r.get("fail")]
    print(f"done: total steps {total}, max span {max(spans)}, "
          f"fails {sum(1 for r in results if r.get('fail'))}")


if __name__ == "__main__":
    main()
