"""Exploration only (not a proof dependency): SAT/XOR search for white-background periodic words.

Fixed period P and drift v = (-2,-2) (the standard drift; other diagonal drifts are rotations).
Coordinates u = x + y, z = x - y.  A visit of phase j in an earlier period lands on pos(i) iff
pos(j) = pos(i) + t v with t >= 1, i.e. z_j = z_i, u_i - u_j in 4Z, u_j < u_i.
Constraint for each phase i (bit w_i = 1: black read, left turn):
    w_i XOR (XOR_{j<i} same_ij) XOR (XOR_j prev_ij) = 0
Positions are one-hot in a bounded box, so UNSAT only means "no such word inside the box".
Optionally block the cyclic rotations of given words (e.g. the standard 104 word).
Writes DIMACS with CryptoMiniSat XOR lines.
usage: python periodic_sat.py P ZMAX UMIN UMAX out.cnf [blockfile] [--free-start] [--plain]
With --free-start the initial heading is free (it must only equal the final heading); by
rotation symmetry this covers every orbit whose drift is a diagonal (+-2,+-2).
With --plain every XOR is expanded into ordinary clauses (chained through auxiliary variables), so
plain CNF solvers such as CaDiCaL can be used.
"""
import sys

def main():
    P, ZMAX, UMIN, UMAX, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
    rest = sys.argv[6:]
    free_start = "--free-start" in rest
    plain = "--plain" in rest
    rest = [a for a in rest if a not in ("--free-start", "--plain")]
    block = open(rest[0]).read().split() if rest else []
    nv = [0]
    def new():
        nv[0] += 1
        return nv[0]
    cls, xors = [], []
    Zs = list(range(-ZMAX, ZMAX + 1)); Us = list(range(UMIN, UMAX + 1))
    W = [new() for _ in range(P)]
    D = [[new() for _ in range(4)] for _ in range(P + 1)]          # N E S W
    Z = [{c: new() for c in Zs} for _ in range(P + 1)]
    U = [{c: new() for c in Us} for _ in range(P + 1)]
    def exactly_one(vs):
        cls.append(list(vs))
        for a in range(len(vs)):
            for b in range(a + 1, len(vs)):
                cls.append([-vs[a], -vs[b]])
    for i in range(P + 1):
        exactly_one(D[i]); exactly_one(list(Z[i].values())); exactly_one(list(U[i].values()))
    if free_start:
        for d in range(4):
            cls.append([-D[0][d], D[P][d]]); cls.append([D[0][d], -D[P][d]])
    else:
        cls.append([D[0][0]]); cls.append([D[P][0]])
    cls.append([Z[0][0]]); cls.append([U[0][0]])
    cls.append([Z[P][0]]); cls.append([U[P][-4]])                    # v = (-2,-2): u -4, z 0
    # turning: black (w) -> left = d-1, white -> right = d+1
    for i in range(P):
        for d in range(4):
            cls.append([-D[i][d], -W[i], D[i + 1][(d + 3) % 4]])
            cls.append([-D[i][d], W[i], D[i + 1][(d + 1) % 4]])
    # moving with the new heading: N (0,+1): u+1 z-1; E (+1,0): u+1 z+1; S: u-1 z+1; W: u-1 z-1
    du = [1, 1, -1, -1]; dz = [-1, 1, 1, -1]
    for i in range(P):
        for d in range(4):
            for c in Zs:
                c2 = c + dz[d]
                if c2 in Z[i + 1]:
                    cls.append([-D[i + 1][d], -Z[i][c], Z[i + 1][c2]])
                else:
                    cls.append([-D[i + 1][d], -Z[i][c]])
            for c in Us:
                c2 = c + du[d]
                if c2 in U[i + 1]:
                    cls.append([-D[i + 1][d], -U[i][c], U[i + 1][c2]])
                else:
                    cls.append([-D[i + 1][d], -U[i][c]])
    # pair indicators
    def defined_or(terms):
        """fresh var e with e <-> OR(terms), each term a pair (a, b) meaning a AND b"""
        e = new()
        ts = []
        for a, b in terms:
            t = new()
            cls.append([-t, a]); cls.append([-t, b]); cls.append([t, -a, -b])
            ts.append(t)
            cls.append([e, -t])
        cls.append([-e] + ts)
        return e
    zeq = {}
    def get_zeq(i, j):
        k = (min(i, j), max(i, j))
        if k not in zeq:
            zeq[k] = defined_or([(Z[i][c], Z[j][c]) for c in Zs])
        return zeq[k]
    for i in range(P):
        parts = [-W[i]]  # x-lines assert XOR = true; negate one literal to assert XOR = 0
        for j in range(P):
            if j == i:
                continue
            ze = get_zeq(i, j)
            if j < i:   # same cell, same period, earlier
                ue = defined_or([(U[i][c], U[j][c]) for c in Us])
                s = new(); cls += [[-s, ze], [-s, ue], [s, -ze, -ue]]
                parts.append(s)
            # earlier period: u_i - u_j in 4Z_{>0}
            terms = [(U[i][a], U[j][b]) for a in Us for b in Us if a > b and (a - b) % 4 == 0]
            ul = defined_or(terms) if terms else None
            if ul is not None:
                p = new(); cls += [[-p, ze], [-p, ul], [p, -ze, -ul]]
                parts.append(p)
        # also the phase j = i of earlier periods (pos(i) + t v = pos(i) is impossible for t >= 1)
        xors.append(parts)
    for word in block:
        assert len(word) == P
        for r in range(P):
            rot = word[r:] + word[:r]
            cls.append([(-W[i] if rot[i] == "1" else W[i]) for i in range(P)])
    def parity_clauses(lits, parity):
        # forbid every assignment of the literals whose XOR differs from `parity`
        out_cls = []
        for m in range(1 << len(lits)):
            vals = [(m >> k) & 1 for k in range(len(lits))]
            if sum(vals) % 2 != parity:
                out_cls.append([(-l if v else l) for l, v in zip(lits, vals)])
        return out_cls
    if plain:
        for x in xors:                       # XOR(x) = true
            lits = list(x)
            while len(lits) > 4:
                a = new()                    # a = l1 xor l2 xor l3
                cls.extend(parity_clauses(lits[:3] + [a], 0))
                lits = [a] + lits[3:]
            cls.extend(parity_clauses(lits, 1))
        xors = []
    with open(out, "w", newline="\n") as f:
        f.write(f"p cnf {nv[0]} {len(cls) + len(xors)}\n")
        for c in cls:
            f.write(" ".join(map(str, c)) + " 0\n")
        for x in xors:
            f.write("x" + " ".join(map(str, x)) + " 0\n")
    print(f"vars {nv[0]} clauses {len(cls)} xors {len(xors)} W-vars 1..{P}")

if __name__ == "__main__":
    main()
