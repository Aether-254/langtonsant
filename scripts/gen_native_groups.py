"""Grouped assembly of PeriodicNative.All{P} for many blocks (avoids one huge `match`).
Writes PeriodicNative/All{P}G{g}.lean (256 blocks each) and PeriodicNative/All{P}.lean.
usage: python gen_native_groups.py P WIDTH_BITS
"""
import sys
P, wb = int(sys.argv[1]), int(sys.argv[2]); W = 2 ** wb; blocks = 2 ** (P - wb); G = 256
groups = blocks // G
for g in range(groups):
    L = ["import PeriodicWordFast"] + [f"import PeriodicNative.P{P}B{G*g+r}" for r in range(G)]
    L += ["", "namespace LangtonsAnt", "",
          f"theorem fastScan_{P}_group_{g} : forall r, r < {G} -> fastScan {P} {W} ({W} * ({G} * {g} + r)) = true := by",
          "  intro r hr", "  match r, hr with"]
    L += [f"  | {r}, _ => exact fastScan_{P}_{G*g+r}" for r in range(G)]
    L += [f"  | n + {G}, h => exact absurd h (by omega)", "", "end LangtonsAnt", ""]
    open(f"PeriodicNative/All{P}G{g}.lean", "w", encoding="utf-8", newline="\n").write("\n".join(L))
L = ["import PeriodicWordFast"] + [f"import PeriodicNative.All{P}G{g}" for g in range(groups)]
L += ["", "namespace LangtonsAnt", "",
      f"theorem checkNoWords_native_{P} : checkNoWords {P} = true := by",
      f"  apply checkNoWords_of_fastBlocks (width := {W}) (blocks := {blocks}) (by decide) (by decide)",
      "  intro k hk",
      f"  have hq : k / {G} < {groups} := by omega",
      f"  have hr : k % {G} < {G} := Nat.mod_lt _ (by decide)",
      f"  rw [show k = {G} * (k / {G}) + k % {G} by omega]",
      f"  generalize k / {G} = q at hq ⊢",
      f"  generalize k % {G} = r at hr ⊢",
      "  match q, hq with"]
L += [f"  | {g}, _ => exact fastScan_{P}_group_{g} r hr" for g in range(groups)]
L += [f"  | n + {groups}, h => exact absurd h (by omega)", "", "end LangtonsAnt", ""]
open(f"PeriodicNative/All{P}.lean", "w", encoding="utf-8", newline="\n").write("\n".join(L))
print(f"P={P}: {groups} groups of {G}")
