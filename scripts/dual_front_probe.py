"""Look for axis words satisfying a deliberate relaxation, not finite-white highways.

Each full translation class must alternate, but its first read may be black.
Both diagonal record fronts must have the full 100001 local gadget. A hit
refutes the use of those constraints alone, not HighwayConjecture.
"""

import argparse
import json
import time


MOVES = ((0, 1), (1, 0), (0, -1), (-1, 0))
GADGET = (1, 0, 0, 0, 0, 1)


def analyze(bits, positions, headings, drift, require_supported=False):
    period = len(bits)
    a, b = drift
    if a <= 0 or b != 0 or period < 4 * a:
        return None
    records = []
    for sy in (1, -1):
        levels = [x + sy * y for x, y in positions]
        maximum = max(levels) - a
        starts = []
        for i, level in enumerate(levels):
            if level <= maximum:
                continue
            maximum = level
            if bits[i] != 0:
                return None
            dx, dy = MOVES[(headings[i] + 1) % 4]
            if dx + sy * dy == 1:
                if tuple(bits[(i - 1 + j) % period] for j in range(6)) != GADGET:
                    return None
                starts.append(i)
        if len(starts) * 2 != a:
            return None
        records.append(starts)
    groups = {}
    for i, (x, y) in enumerate(positions):
        groups.setdefault((x % a, y), []).append((i - period * (x // a), i))
    black_first = []
    ranks = {}
    for key, events in groups.items():
        events.sort()
        first = bits[events[0][1]]
        if any(bits[i] != (first ^ (rank % 2)) for rank, (_, i) in enumerate(events)):
            return None
        if first:
            black_first.append(list(key))
        for rank, (_, i) in enumerate(events):
            ranks[i] = rank
    supports = [[ranks[(i - 1) % period] for i in starts] for starts in records]
    if require_supported and any(rank == 0 for front in supports for rank in front):
        return None
    return {
        "period": period,
        "word": "".join(map(str, bits)),
        "initial_heading": "east",
        "drift": list(drift),
        "record_pair_starts": records,
        "preceding_black_ranks": supports,
        "black_first_classes": black_first,
        "finite_white_consistent": not black_first,
    }


def search(period, deadline, require_supported=False):
    board = {}
    positions = []
    headings = []
    bits = []
    nodes = 0

    def visit(x, y, heading, maximum, required):
        nonlocal nodes
        nodes += 1
        if nodes % 8192 == 0 and time.monotonic() >= deadline:
            raise TimeoutError
        n = len(bits)
        if n == period:
            if heading == 1:
                return analyze(bits, positions, headings, (x, y), require_supported)
            return None
        remaining = period - n
        if abs(y) > remaining or x + remaining < 2 or maximum > period // 4:
            return None
        if max(0, maximum - x) + abs(y) > remaining:
            return None
        level = x + y
        if level > maximum:
            maximum = level
            requirements = {n: 0}
            dx, dy = MOVES[(heading + 1) % 4]
            if dx + dy == 1:
                if n == 0 or bits[n - 1] != 1:
                    return None
                requirements = {(n + j) % period: bit for j, bit in enumerate((0, 0, 0, 0, 1))}
            changed = list(required)
            for j, bit in requirements.items():
                if (j < n and bits[j] != bit) or (changed[j] is not None and changed[j] != bit):
                    return None
                changed[j] = bit
            required = tuple(changed)
        p = (x, y)
        old = board.get(p)
        choices = (required[n],) if required[n] is not None else ((old,) if old is not None else (0, 1))
        for bit in choices:
            if old is not None and old != bit:
                continue
            board[p] = 1 - bit
            bits.append(bit)
            positions.append(p)
            headings.append(heading)
            next_heading = (heading + (1 if bit == 0 else -1)) % 4
            dx, dy = MOVES[next_heading]
            result = visit(x + dx, y + dy, next_heading, maximum, required)
            if result is not None:
                return result
            headings.pop()
            positions.pop()
            bits.pop()
        if old is None:
            board.pop(p, None)
        else:
            board[p] = old
        return None

    # Phase zero is the L immediately before an F_plus record pair. Its
    # preceding bi-infinite maximum is zero, as is the current level.
    result = visit(0, 0, 1, 0, GADGET + (None,) * (period - len(GADGET)))
    return result, nodes


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-period", type=int, default=26)
    parser.add_argument("--seconds", type=float, default=30)
    parser.add_argument("--require-supported-fronts", action="store_true")
    parser.add_argument("--word", help="Verify one binary word from an east-facing origin instead of searching")
    args = parser.parse_args()
    if args.word is not None:
        if not args.word or any(bit not in "01" for bit in args.word):
            parser.error("--word must be a nonempty binary string")
        bits = [int(bit) for bit in args.word]
        positions, headings = [], []
        x, y, heading = 0, 0, 1
        for bit in bits:
            positions.append((x, y))
            headings.append(heading)
            heading = (heading + (1 if bit == 0 else -1)) % 4
            dx, dy = MOVES[heading]
            x, y = x + dx, y + dy
        hit = analyze(bits, positions, headings, (x, y), args.require_supported_fronts) if heading == 1 else None
        print(json.dumps({"verified_word": args.word, "hit": hit}), flush=True)
        return
    deadline = time.monotonic() + args.seconds
    for period in range(8, args.max_period + 1, 2):
        try:
            result, nodes = search(period, deadline, args.require_supported_fronts)
        except TimeoutError:
            print(json.dumps({"status": "incomplete", "period": period}), flush=True)
            return
        print(json.dumps({"searched_period": period, "nodes": nodes, "hit": result}), flush=True)
        if result is not None:
            return


if __name__ == "__main__":
    main()
