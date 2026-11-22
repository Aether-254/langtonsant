"""Exploration helper: expand CryptoMiniSat XOR lines ("x l1 l2 ... 0", meaning XOR = true) of a
DIMACS file into plain clauses, chaining long XORs through fresh variables.
usage: python xor2cnf.py in.cnf out.cnf
"""
import sys

def parity_clauses(lits, parity):
    out = []
    for m in range(1 << len(lits)):
        vals = [(m >> k) & 1 for k in range(len(lits))]
        if sum(vals) % 2 != parity:
            out.append([(-l if v else l) for l, v in zip(lits, vals)])
    return out

def main():
    src, dst = sys.argv[1], sys.argv[2]
    nv, cls = 0, []
    for line in open(src):
        line = line.strip()
        if not line or line.startswith("c"):
            continue
        if line.startswith("p"):
            nv = int(line.split()[2]); continue
        if line.startswith("x"):
            lits = [int(t) for t in line[1:].split()][:-1]
            while len(lits) > 4:
                nv += 1
                cls.extend(parity_clauses(lits[:3] + [nv], 0))
                lits = [nv] + lits[3:]
            cls.extend(parity_clauses(lits, 1))
        else:
            cls.append([int(t) for t in line.split()][:-1])
    with open(dst, "w", newline="\n") as f:
        f.write(f"p cnf {nv} {len(cls)}\n")
        for c in cls:
            f.write(" ".join(map(str, c)) + " 0\n")
    print(f"vars {nv} clauses {len(cls)}")

if __name__ == "__main__":
    main()
