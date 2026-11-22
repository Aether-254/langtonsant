"""Generate PeriodicNative/ modules: native_decide block scans for even P and their union.

Each block module proves `fastScan P W (W * k) = true` by `native_decide`; the union module
proves `checkNoWords P = true` from all blocks with `checkNoWords_of_fastBlocks`.
usage: python gen_periodic_native.py PMIN PMAX
"""
import os, sys

def width(P):
    if P <= 22: return P
    if P <= 26: return 22
    return 24

def main():
    pmin, pmax = int(sys.argv[1]), int(sys.argv[2])
    os.makedirs("PeriodicNative", exist_ok=True)
    for P in range(pmin, pmax + 1, 2):
        wb = width(P); W = 2 ** wb; blocks = 2 ** (P - wb)
        for k in range(blocks):
            open(f"PeriodicNative/P{P}B{k}.lean", "w", encoding="utf-8", newline="\n").write(
                f"import PeriodicWordFast\n\nnamespace LangtonsAnt\n\n"
                f"theorem fastScan_{P}_{k} : fastScan {P} {W} ({W} * {k}) = true := by native_decide\n\n"
                f"end LangtonsAnt\n")
        lines = ["import PeriodicWordFast"] + [f"import PeriodicNative.P{P}B{k}" for k in range(blocks)]
        lines += ["", "namespace LangtonsAnt", "",
                  *(["set_option maxRecDepth 100000 in", "set_option maxHeartbeats 0 in"] if blocks > 256 else []),
                  f"theorem checkNoWords_native_{P} : checkNoWords {P} = true := by",
                  f"  apply checkNoWords_of_fastBlocks (width := {W}) (blocks := {blocks}) (by decide) (by decide)",
                  "  intro k hk",
                  "  match k, hk with"]
        for k in range(blocks):
            lines.append(f"  | {k}, _ => exact fastScan_{P}_{k}")
        lines.append(f"  | n + {blocks}, h => exact absurd h (by omega)")
        lines += ["", "end LangtonsAnt", ""]
        open(f"PeriodicNative/All{P}.lean", "w", encoding="utf-8", newline="\n").write("\n".join(lines))
        print(f"P={P}: {blocks} blocks of 2^{wb}")

if __name__ == "__main__":
    main()
