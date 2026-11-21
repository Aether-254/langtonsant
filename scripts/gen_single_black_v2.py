"""Regenerate SingleBlackEarly with per-cell certificate style.

Cells listed in DONE files keep their existing (already compiled) `checkSingleBlack` module;
all other cells get a `checkSingleBlackFast` module (FastCell.lean).  Group files use the
matching soundness lemma.  Parameters come from scripts/find_single_black.py (untrusted).
usage: python gen_single_black_v2.py PARAMS_JSON NGROUPS OUTDIR DONE_FILE...
"""
import json, os, sys

def pt(p):
    return f"({p[0]}, {p[1]})"

params = json.load(open(sys.argv[1]))
ngroups = int(sys.argv[2]); outdir = sys.argv[3]
done = set()
for f in sys.argv[4:]:
    done |= {int(x) for x in open(f).read().split()}
style = {k: ("old" if k in done else "fast") for k in range(len(params))}
for k, r in enumerate(params):
    if style[k] == "old":
        continue
    lines = ["import FastCell", "", "namespace LangtonsAnt", "",
             "set_option maxRecDepth 1000000 in", "set_option maxHeartbeats 0 in",
             f"theorem sbCell{k:04d} : checkSingleBlackFast {pt(r['q'])} {r['T']} .{r['dir']} "
             f"{pt(r['w'])} {pt(r['o'])} = true := by",
             "  decide +kernel", "", "end LangtonsAnt", ""]
    open(os.path.join(outdir, f"C{k:04d}.lean"), "w", encoding="utf-8").write("\n".join(lines))
size = (len(params) + ngroups - 1) // ngroups
groups = [list(range(g * size, min(len(params), (g + 1) * size))) for g in range(ngroups)]
groups = [g for g in groups if g]
for g, ks in enumerate(groups):
    sound = {"old": "checkSingleBlack_sound", "fast": "checkSingleBlackFast_sound"}
    lines = ["import FastCell"] + [f"import SingleBlackEarly.C{k:04d}" for k in ks] + [
        "", "namespace LangtonsAnt", "",
        f"def sbGroup{g:02d} : List Point :=",
        "  [" + ", ".join(pt(params[k]["q"]) for k in ks) + "]", "",
        f"theorem sbGroup{g:02d}_ok : forall q, q ∈ sbGroup{g:02d} -> EventuallyStandard (singleBlack q) := by",
        "  intro q hq",
        f"  simp only [sbGroup{g:02d}, List.mem_cons, List.not_mem_nil, or_false] at hq",
        "  rcases hq with " + " | ".join(["rfl"] * len(ks)),
    ] + [f"  · exact {sound[style[k]]} sbCell{k:04d}" for k in ks] + ["", "end LangtonsAnt", ""]
    open(os.path.join(outdir, f"G{g:02d}.lean"), "w", encoding="utf-8").write("\n".join(lines))
json.dump(style, open(os.path.join("scratch-codex", "cell-style.json"), "w"))
print(f"old {sum(1 for v in style.values() if v=='old')}, fast {sum(1 for v in style.values() if v=='fast')}")
