"""Generate the segmented phase-49 prefix check (exploration output, untrusted).

Reproduces `trailPackedInput` exactly: the seed run for 1401 steps (list semantics = set
semantics for membership), flip of the current cell, translation by (8,16), half-turn rotation,
packed encoding with bitIndex (x+64)*128 + (y+64).  Then it runs `PackedState.step` and records
a literal state every SEG steps.  Every literal is re-checked by the kernel.
usage: python gen_k2_segments.py SEG
"""
import sys
sys.set_int_max_str_digits(0)

SEED = [(-2, -1), (2, -2), (2, -3), (2, -4), (2, -6), (1, -1), (-1, -4), (3, -5), (1, -5),
        (0, -3), (0, -2), (1, -3), (4, -4), (1, -4), (-1, 0), (0, -5), (0, -1), (0, 0), (-1, 1),
        (-2, 0), (2, -5), (1, -6), (-1, -3)]
RIGHT = {"north": "east", "east": "south", "south": "west", "west": "north"}
LEFT = {"north": "west", "east": "north", "south": "east", "west": "south"}
DELTA = {"north": (0, 1), "east": (1, 0), "south": (0, -1), "west": (-1, 0)}
FLIP = 104 * 13 + 49
DELAY = 52421

def step_set(black, pos, d):
    c = pos in black
    d = LEFT[d] if c else RIGHT[d]
    (black.discard if c else black.add)(pos)
    return (pos[0] + DELTA[d][0], pos[1] + DELTA[d][1]), d

def bit_index(p):
    return (p[0] + 64) * 128 + (p[1] + 64)

def inbox(p):
    return -64 <= p[0] < 64 and -64 <= p[1] < 64

def pt(p):
    return f"({p[0]}, {p[1]})"

def main():
    SEG = int(sys.argv[1])
    black = set(SEED); pos = (0, 0); d = "north"
    for _ in range(FLIP):
        pos, d = step_set(black, pos, d)
    black ^= {pos}                                   # flippedAt: toggle the current cell
    black = {(x + 8, y + 16) for (x, y) in black}    # translate (8,16)
    pos = (pos[0] + 8, pos[1] + 16)
    black = {(-x, -y) for (x, y) in black}           # rotate south
    pos = (-pos[0], -pos[1])
    d = RIGHT[RIGHT[d]]                              # rotateDir south = right twice
    bits = 0
    for p in black:
        assert inbox(p)
        bits |= 1 << bit_index(p)
    K = (DELAY - 1) // SEG
    states = []
    for t in range(1, K * SEG + 1):
        assert inbox(pos)
        i = bit_index(pos)
        d = LEFT[d] if (bits >> i) & 1 else RIGHT[d]
        bits ^= 1 << i
        pos = (pos[0] + DELTA[d][0], pos[1] + DELTA[d][1])
        if t % SEG == 0:
            states.append((bits, pos, d))
    for i, (b, p, dd) in enumerate(states, start=1):
        prev = "trailPackedInput.toPacked" if i == 1 else f"k2State{i-1}"
        imp = "Phase49Seg" if i == 1 else f"Phase49K2_{i-1}"
        open(f"Phase49K2_{i}.lean", "w", encoding="utf-8", newline="\n").write("\n".join([
            f"import {imp}", "", "/-! Segment of the phase-49 prefix check (generated). -/", "",
            "namespace LangtonsAnt", "",
            f"def k2State{i} : PackedState := ⟨{b}, {pt(p)}, .{dd}⟩", "",
            "set_option maxRecDepth 1000000 in", "set_option maxHeartbeats 0 in",
            f"theorem k2Seg{i} : checkTrailSeg g49 {SEG} {prev} k2State{i} = true := by",
            "  decide +kernel", "", "end LangtonsAnt", ""]))
    last = DELAY - K * SEG
    lines = [f"import Phase49K2_{K}", "",
             "/-! Final segment and assembly of the phase-49 prefix check (generated). -/", "",
             "namespace LangtonsAnt", "",
             "set_option maxRecDepth 1000000 in", "set_option maxHeartbeats 0 in",
             f"theorem k2Final : checkTrailPrefix g49 (-26) trailPackedTarget {last} k2State{K} = true := by",
             "  decide +kernel", "",
             "theorem trail_prefix_guard (j : Nat) (hj : j < trailDelay) :",
             "    g49 (run trailPackedInput.toPacked.toState j).pos = true := by",
             "  have s1 := checkTrailSeg_sound k2Seg1"]
    for i in range(2, K + 1):
        lines.append(f"  have s{i} := checkTrailSeg_sound k2Seg{i}")
    lines.append("  have sF := checkTrailPrefix_sound k2Final")
    # reached states: r_i : run X0 (SEG*i) = k2State_i.toState
    lines.append("  have r1 : run trailPackedInput.toPacked.toState " + str(SEG) + " = k2State1.toState := s1.2")
    for i in range(2, K + 1):
        lines.append(f"  have r{i} : run trailPackedInput.toPacked.toState {SEG * i} = k2State{i}.toState := by")
        lines.append(f"    rw [show ({SEG * i} : Nat) = {SEG * (i - 1)} + {SEG} from rfl, run_add, r{i-1}]")
        lines.append(f"    exact s{i}.2")
    lines.append("  unfold trailDelay at hj")
    for i in range(1, K + 1):
        lo = SEG * (i - 1)
        if i == 1:
            lines.append(f"  by_cases c1 : j < {SEG}")
            lines.append(f"  · exact s1.1 j c1")
        else:
            lines.append(f"  by_cases c{i} : j < {SEG * i}")
            lines.append(f"  · have hg := guard_shift r{i-1} s{i}.1 (j - {lo}) (by omega)")
            lines.append(f"    rwa [show {lo} + (j - {lo}) = j by omega] at hg")
    lines.append(f"  have hg := guard_shift r{K} sF.1 (j - {SEG * K}) (by omega)")
    lines.append(f"  rwa [show {SEG * K} + (j - {SEG * K}) = j by omega] at hg")
    lines += ["", "theorem trail_prefix_avoid2 (j : Nat) (hj : j < trailDelay) :",
              "    avoidJunk2 (run trailStart j).pos = true := by",
              "  have h := trail_prefix_guard j hj",
              "  rw [trailPackedInput_toState, trailFrame_run] at h",
              "  unfold g49 at h",
              "  rw [trailUnframe_pos] at h",
              "  simp only [Bool.and_eq_true] at h",
              "  exact h.2", "", "end LangtonsAnt", ""]
    open("Phase49K2.lean", "w", encoding="utf-8", newline="\n").write("\n".join(lines))
    print(f"SEG {SEG}: {K} segment modules, final {last} steps")

if __name__ == "__main__":
    main()
