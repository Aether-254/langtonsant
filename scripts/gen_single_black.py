"""Generate Lean files with one kernel-checked certificate per early single black cell.

Input: the JSON produced by scripts/find_single_black.py (untrusted search output).
Output: SingleBlackEarly/ChunkNNN.lean and SingleBlackEarly/Cells.lean.
Every certificate is re-checked by `decide +kernel`; a wrong parameter only makes the
build fail, it cannot produce a false theorem.
"""
import heapq
import json
import os
import sys


def pt(p):
    return f"({p[0]}, {p[1]})"


def main():
    params = json.load(open(sys.argv[1]))
    ngroups = int(sys.argv[2])
    outdir = sys.argv[3]
    remote_frac = float(sys.argv[4])
    remote_max_T = int(sys.argv[5])
    os.makedirs(outdir, exist_ok=True)
    assert all(not r.get("fail") for r in params)
    # one module per cell: memory of the kernel check is released when each process exits
    for k, r in enumerate(params):
        lines = [
            "import SingleBlackCheck",
            "",
            "namespace LangtonsAnt",
            "",
            "set_option maxRecDepth 1000000 in",
            "set_option maxHeartbeats 0 in",
            f"theorem sbCell{k:04d} : checkSingleBlack {pt(r['q'])} {r['T']} .{r['dir']} "
            f"{pt(r['w'])} {pt(r['o'])} = true := by",
            "  decide +kernel",
            "",
            "end LangtonsAnt",
            "",
        ]
        with open(os.path.join(outdir, f"C{k:04d}.lean"), "w", encoding="utf-8") as f:
            f.write("\n".join(lines))
    # groups: contiguous index ranges
    size = (len(params) + ngroups - 1) // ngroups
    groups = [list(range(g * size, min(len(params), (g + 1) * size))) for g in range(ngroups)]
    groups = [g for g in groups if g]
    for g, ks in enumerate(groups):
        lines = ["import SingleBlackCheck"] + [f"import SingleBlackEarly.C{k:04d}" for k in ks] + [
            "",
            "namespace LangtonsAnt",
            "",
            f"def sbGroup{g:02d} : List Point :=",
            "  [" + ", ".join(pt(params[k]["q"]) for k in ks) + "]",
            "",
            f"theorem sbGroup{g:02d}_ok : forall q, q ∈ sbGroup{g:02d} -> EventuallyStandard (singleBlack q) := by",
            "  intro q hq",
            f"  simp only [sbGroup{g:02d}, List.mem_cons, List.not_mem_nil, or_false] at hq",
            "  rcases hq with " + " | ".join(["rfl"] * len(ks)),
        ] + [f"  · exact checkSingleBlack_sound sbCell{k:04d}" for k in ks] + ["", "end LangtonsAnt", ""]
        with open(os.path.join(outdir, f"G{g:02d}.lean"), "w", encoding="utf-8") as f:
            f.write("\n".join(lines))
    n = len(groups)
    lines = ["import SingleBlackCheck"] + [f"import SingleBlackEarly.G{g:02d}" for g in range(n)] + [
        "",
        "/-! Generated: the union of all early single-black cells and their certificates. -/",
        "",
        "namespace LangtonsAnt",
        "",
        "theorem ok_append {P : Point -> Prop} {a b : List Point}",
        "    (ha : forall q, q ∈ a -> P q) (hb : forall q, q ∈ b -> P q) :",
        "    forall q, q ∈ a ++ b -> P q := by",
        "  intro q hq",
        "  rcases List.mem_append.mp hq with h | h",
        "  · exact ha q h",
        "  · exact hb q h",
        "",
        "def earlyCells : List Point :=",
        "  " + " ++ ".join(f"sbGroup{g:02d}" for g in range(n)),
        "",
        "theorem earlyCells_ok : forall q, q ∈ earlyCells -> EventuallyStandard (singleBlack q) := by",
        "  unfold earlyCells",
    ]
    # `++` is left associative, so nest the proof to the left as well
    expr = "sbGroup00_ok"
    for g in range(1, n):
        expr = f"(ok_append {expr} sbGroup{g:02d}_ok)"
    lines += [f"  exact {expr}", "", "end LangtonsAnt", ""]
    with open(os.path.join(outdir, "Cells.lean"), "w", encoding="utf-8") as f:
        f.write("\n".join(lines))
    # machine assignment, largest first; remote only takes cells with T <= remote_max_T
    order = sorted(range(len(params)), key=lambda k: -params[k]["T"])
    total = sum(r["T"] for r in params)
    remote, rload = [], 0
    for k in order:
        if params[k]["T"] <= remote_max_T and rload + params[k]["T"] <= remote_frac * total and k % 3 == 0:
            remote.append(k)
            rload += params[k]["T"]
    rs = set(remote)
    local = [k for k in order if k not in rs]
    open(os.path.join(outdir, "..", "scratch-codex", "cells-local.txt"), "w").write("\n".join(map(str, local)))
    open(os.path.join(outdir, "..", "scratch-codex", "cells-remote.txt"), "w").write("\n".join(map(str, remote)))
    print(f"{len(params)} cells, {n} groups; local {len(local)} cells {total - rload} steps; "
          f"remote {len(remote)} cells {rload} steps")


if __name__ == "__main__":
    main()
