"""Generate segmented certificates for long single-black cells (exploration output, untrusted).

For cell k with parameters (q, T, r, w, o): simulate the frame state of `singleBlackFrame q r w`
exactly as `WideState.step` does, record literal states every SEG steps, and write
  SingleBlackEarly/S{k}_{i}.lean : checkSegment SEG prev = literal state i   (one kernel check)
  SingleBlackEarly/C{k}.lean     : last entry check + chaining -> EventuallyStandard
usage: python gen_segments.py PARAMS_JSON LIST_FILE SEG
"""
import json, sys
sys.set_int_max_str_digits(0)

def turn(black, d):
    L = {"north": "west", "east": "north", "south": "east", "west": "south"}
    R = {"north": "east", "east": "south", "south": "west", "west": "north"}
    return L[d] if black else R[d]

def move(p, d):
    return {"north": (p[0], p[1] + 1), "east": (p[0] + 1, p[1]),
            "south": (p[0], p[1] - 1), "west": (p[0] - 1, p[1])}[d]

def rot_point(r, p):
    x, y = p
    return {"north": (x, y), "east": (y, -x), "south": (-x, -y), "west": (-y, x)}[r]

RIGHT = {"north": "east", "east": "south", "south": "west", "west": "north"}
LEFT = {"north": "west", "east": "north", "south": "east", "west": "south"}

def rot_dir(r, d):
    if r == "north": return d
    if r == "east": return RIGHT[d]
    if r == "south": return RIGHT[RIGHT[d]]
    return LEFT[d]

INV = {"north": "north", "east": "west", "south": "south", "west": "east"}

def idx(p):
    return (p[0] + 128) * 256 + (p[1] + 128)

def inwide(p):
    return -128 <= p[0] < 128 and -128 <= p[1] < 128

def pt(p):
    return f"({p[0]}, {p[1]})"

def main():
    params = json.load(open(sys.argv[1]))
    cells = [int(x) for x in open(sys.argv[2]).read().split()]
    SEG = int(sys.argv[3])
    plan = {}
    for k in cells:
        x = params[k]
        q, T, r, w, o = tuple(x["q"]), x["T"], x["dir"], tuple(x["w"]), tuple(x["o"])
        R = INV[r]
        black = rot_point(R, (q[0] + w[0], q[1] + w[1]))
        pos = rot_point(R, w)
        d = rot_dir(R, "north")
        bits = 1 << idx(black)
        K = (T - 1) // SEG
        states = []
        for t in range(1, K * SEG + 1):
            assert inwide(pos)
            i = idx(pos)
            d = turn((bits >> i) & 1 == 1, d)
            bits ^= 1 << i
            pos = move(pos, d)
            if t % SEG == 0:
                states.append((bits, pos, d))
        plan[k] = K
        for i, (b, p, dd) in enumerate(states, start=1):
            prev = f"(singleBlackFrame {pt(q)} .{r} {pt(w)}).toWide" if i == 1 else f"sbSegState{k:04d}_{i-1}"
            imp = "SegmentCheck" if i == 1 else f"SingleBlackEarly.S{k:04d}_{i-1}"
            open(f"SingleBlackEarly/S{k:04d}_{i}.lean", "w", encoding="utf-8").write("\n".join([
                f"import {imp}", "", "namespace LangtonsAnt", "",
                f"def sbSegState{k:04d}_{i} : WideState :=",
                f"  ⟨{b}, {pt(p)}, .{dd}⟩", "",
                "set_option maxRecDepth 1000000 in", "set_option maxHeartbeats 0 in",
                f"theorem sbSeg{k:04d}_{i} : checkSegment {SEG} {prev} sbSegState{k:04d}_{i}.bits",
                f"    sbSegState{k:04d}_{i}.pos sbSegState{k:04d}_{i}.dir = true := by",
                "  decide +kernel", "", "end LangtonsAnt", ""]))
        last = T - K * SEG
        chain = ["  have h1 := checkSegment_sound' sbSeg{:04d}_1".format(k)]
        for i in range(2, K + 1):
            chain.append(f"  have h{i} := segment_chain h{i-1} (checkSegment_sound' sbSeg{k:04d}_{i})")
        imp = f"SingleBlackEarly.S{k:04d}_{K}" if K >= 1 else "SegmentCheck"
        lines = [f"import {imp}", "", "namespace LangtonsAnt", "",
                 "set_option maxRecDepth 1000000 in", "set_option maxHeartbeats 0 in",
                 f"theorem sbBox{k:04d} : (singleBlackFrame {pt(q)} .{r} {pt(w)}).black.all",
                 "    (fun p => decide (InWide p)) = true := by", "  decide +kernel", "",
                 "set_option maxRecDepth 1000000 in", "set_option maxHeartbeats 0 in",
                 f"theorem sbEntry{k:04d} : checkWideEntry (weight ({pt(o)} : Point))",
                 f"    (highwaySeed.translate {pt(o)}) {last} sbSegState{k:04d}_{K} = true := by",
                 "  decide +kernel", "",
                 f"theorem sbCell{k:04d} : EventuallyStandard (singleBlack {pt(q)}) := by"] + chain + [
                 f"  exact singleBlack_of_segments (o := {pt(o)}) sbBox{k:04d} h{K} sbEntry{k:04d}",
                 "", "end LangtonsAnt", ""]
        assert K >= 1
        open(f"SingleBlackEarly/C{k:04d}.lean", "w", encoding="utf-8").write("\n".join(lines))
    json.dump(plan, open("scratch-codex/segment-plan.json", "w"))
    print(f"{len(cells)} cells, segments {sum(plan.values())}, SEG {SEG}")

if __name__ == "__main__":
    main()
