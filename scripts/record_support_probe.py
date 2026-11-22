"""Inspect genuine support excursions on the finite all-white orbit.

Finite observations are used only as counterexamples to proposed local rules.
They do not certify a periodic tail or a universal bound.
"""

import argparse
import json
from collections import Counter


MOVES = ((0, 1), (1, 0), (0, -1), (-1, 0))
SIGNS = ((1, 1), (1, -1), (-1, 1), (-1, -1))
STANDARD_WORD = (
    "LLRLRRRRLRLLLLRRRRLRRLRRRRLLLLRLRRRRLRRRRLLLLRLRRRRLRLLRRLLLLRRLLRRRRLLRRLRLLRLLRLRLLRRRRLLRLLRRRRLLRRRR"
)


def standard_profile():
    positions, headings = [], []
    x = y = heading = 0
    for color in STANDARD_WORD:
        positions.append((x, y))
        headings.append(heading)
        heading = (heading + (-1 if color == "L" else 1)) % 4
        dx, dy = MOVES[heading]
        x, y = x + dx, y + dy
    period = len(STANDARD_WORD)
    assert period == 104 and (x, y, heading) == (-2, -2, 0)
    levels = [-a - b for a, b in positions]
    maximum = max(levels) - 4
    records, pairs = [], []
    for i, level in enumerate(levels):
        if level <= maximum:
            continue
        maximum = level
        records.append(i)
        dx, dy = MOVES[(headings[i] + 1) % 4]
        if -dx - dy != 1:
            continue
        m = i - 1
        px, py = positions[m]
        earlier = []
        for j, (qx, qy) in enumerate(positions):
            if qx - px != qy - py or (qx - px) % 2:
                continue
            shift = (qx - px) // -2
            time = j - period * shift
            if time < m:
                earlier.append((time, j, -shift))
        assert len(earlier) == 1
        time, j, shift = earlier[0]
        assert STANDARD_WORD[j] == "R" and STANDARD_WORD[m] == "L"
        assert headings[j] == headings[m]
        pairs.append({"record": i, "base": m, "source_phase": j,
                      "source_period_offset": shift, "gap": m - time})
    return {"period": period, "drift": [x, y], "records": records, "pairs": pairs}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--steps", type=int, default=20000)
    args = parser.parse_args()
    board = set()
    last_visit = {}
    visit_count = Counter()
    maxima = [0] * 4
    supports = []
    positions, headings = [], []
    x = y = heading = 0
    for t in range(args.steps):
        p = (x, y)
        black = p in board
        positions.append(p)
        headings.append(heading)
        direction = (heading + (-1 if black else 1)) % 4
        dx, dy = MOVES[direction]
        q = (x + dx, y + dy)
        for k, (sx, sy) in enumerate(SIGNS):
            maxima[k] = max(maxima[k], sx * x + sy * y)
            if black and sx * q[0] + sy * q[1] > maxima[k]:
                j = last_visit[p]
                assert visit_count[p] == 1
                assert positions[j] == p and headings[j] == heading
                assert all(sx * a + sy * b <= sx * x + sy * y for a, b in positions[j:t + 1])
                supports.append({"start": j, "end": t, "signs": [sx, sy], "cell": list(p)})
        last_visit[p] = t
        visit_count[p] += 1
        if black:
            board.remove(p)
        else:
            board.add(p)
        x, y, heading = q[0], q[1], direction

    crossing = None
    for i, first in enumerate(supports):
        for second in supports[i + 1:]:
            if first["signs"] == second["signs"]:
                continue
            if first["start"] < second["start"] < first["end"] < second["end"]:
                crossing = [first, second]
                break
        if crossing is not None:
            break
    late = [item for item in supports if item["start"] >= 12080]
    last_front = {}
    failed_links = []
    for item in supports:
        front = tuple(item["signs"])
        previous = last_front.get(front)
        if previous is not None:
            assert previous["end"] < item["start"]
            if item["start"] != previous["end"] + 2:
                failed_links.append({"previous": previous, "current": item})
        last_front[front] = item
    print(json.dumps({
        "steps": args.steps,
        "support_count": len(supports),
        "all_gap_histogram": sorted(Counter(item["end"] - item["start"] for item in supports).items()),
        "late_gap_histogram": sorted(Counter(item["end"] - item["start"] for item in late).items()),
        "crossing_distinct_fronts": crossing,
        "first_late_supports": late[:6],
        "failed_source_link_count": len(failed_links),
        "first_failed_source_links": failed_links[:3],
        "standard_cyclic_profile": standard_profile(),
    }), flush=True)


if __name__ == "__main__":
    main()
