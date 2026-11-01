"""Generate RamseyIncrement/R1658/Data.lean from the 1657-vertex colouring.

    python -B gen/gen_data.py GRAPH [--out PATH] [--flip u:v ...] [--allow-other-sha]

Reads the colouring (n lines of n characters, 1 = red), checks that vertices 0-1595 are
M(797) in the vertex order of r1212-1642, finds the type of each of the 61 added vertices on
V° (copy of a certificate vertex, constant red, constant blue), and writes the core tables:

  vt      type code of added vertex f: t < 20 copies core vertex t, 20 constant red, 21 constant blue
  rowR    red rows of the 81 core vertices (c0..c9, i0..i9, then the added vertices)
  cst*    the constant-red / constant-blue core positions
  bad*    conflict rows (checked against their definition in Checks.lean, so not trusted)

It also evaluates the finite checks that Checks.lean has the kernel evaluate, with the same
algorithms, and prints a summary (exit 1 if a check fails).  --flip changes edges before
anything else, for negative controls; the output then goes only where --out says.
"""
import argparse
import hashlib
import json
import sys
from pathlib import Path

EXPECTED_SHA = "a3eb1cd2c1f67eb14f2fe2e207c64292616df3fa0b0d95454db4d4e614411219"
P = 797
NV = 1596
C = [930, 926, 1573, 1338, 1479, 1483, 1492, 1582, 1586, 1595]
I = [1061, 1588, 1576, 1549, 1554, 1594, 1472, 1557, 1079, 1267]
CERT = C + I
NCORE = 81


def mathon_red(u, v, sq):
    """M(797): A_x = x, B_x = 797 + x, a = 1594, b = 1595 (as in r1212-1642)."""
    if u == v:
        return 0
    if u > v:
        u, v = v, u
    if v < 2 * P:
        x, y = u % P, v % P
        d = (x - y) % P
        if (u < P) == (v < P):
            return 1 if d and sq[d] else 0
        return 1 if d and not sq[d] else 0
    if u < 2 * P:  # one of a, b
        return 1 if (v == 1594 and u < P) or (v == 1595 and u >= P) else 0
    return 0  # a b


def lean_hex(rows, width):
    value = 0
    for i, r in enumerate(rows):
        assert 0 <= r < 1 << width
        value |= r << (width * i)
    return hex(value)


# --- Search.lean's noClique, ported line by line (used only to report the search size)
def log2(x):
    return x.bit_length() - 1


def no_clique(row, t, P_, counter):
    counter[0] += 1
    if t == 0:
        return False
    if P_ == 0:
        return True
    t1 = t - 1
    U, L = P_, 0
    for _ in range(t1):  # colourUnion row t1 P 0
        Q, S, f = U, 0, 256
        while f > 0 and Q != 0:  # greedy row 256 U 0
            v = log2(Q)
            Q, S, f = Q ^ (Q & (row[v] | (1 << v))), S | (1 << v), f - 1
        U, L = U ^ S, L | S
    B = P_ ^ (P_ & L)
    if B == 0:
        return True
    R, f = P_, 256
    while True:  # loopBits
        if f == 0:
            return False
        if B == 0:
            return True
        v = log2(B)
        if not no_clique(row, t1, R & row[v], counter):
            return False
        R, B, f = R ^ (R & (1 << v)), B ^ (1 << v), f - 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("graph")
    ap.add_argument("--out", default=str(Path(__file__).resolve().parent.parent
                                         / "RamseyIncrement" / "R1658" / "Data.lean"))
    ap.add_argument("--flip", action="append", default=[])
    ap.add_argument("--allow-other-sha", action="store_true")
    ap.add_argument("--summary", default=None, help="write the summary JSON here")
    args = ap.parse_args()

    raw = Path(args.graph).read_bytes()
    sha = hashlib.sha256(raw).hexdigest()
    if sha != EXPECTED_SHA and not args.allow_other_sha:
        sys.exit(f"unexpected SHA-256 {sha}")
    lines = raw.split(b"\n")
    if lines[-1] != b"" or any(len(l) != len(lines) - 1 for l in lines[:-1]):
        sys.exit("expected n LF-terminated lines of n characters")
    n = len(lines) - 1
    if n != NV + 61:
        sys.exit(f"expected 1657 vertices, got {n}")
    O = [bytearray(c - 48 for c in l) for l in lines[:-1]]
    if any(set(row) - {0, 1} for row in O):
        sys.exit("characters must be 0 or 1")
    for spec in args.flip:
        u, v = map(int, spec.split(":"))
        assert u != v
        O[u][v] ^= 1
        O[v][u] ^= 1
        print(f"FLIPPED {u}-{v}: now {'red' if O[u][v] else 'blue'}")
    for u in range(n):
        if O[u][u]:
            sys.exit("nonzero diagonal")
        for v in range(u):
            if O[u][v] != O[v][u]:
                sys.exit("not symmetric")

    sq = [False] * P
    for x in range(1, P):
        sq[x * x % P] = True
    for u in range(NV):
        row = O[u]
        for v in range(u):
            if row[v] != mathon_red(u, v, sq):
                sys.exit(f"vertex pair {u},{v} differs from M(797)")
    print("vertices 0..1595: M(797)")

    cert_set = set(CERT)
    V0 = [v for v in range(NV) if v not in cert_set]
    types = []
    for f in range(NV, n):
        row = [O[f][v] for v in V0]
        if all(row):
            types.append(20)
        elif not any(row):
            types.append(21)
        else:
            hits = [j for j, g in enumerate(CERT) if all(O[g][v] == x for v, x in zip(V0, row))]
            if len(hits) != 1:
                sys.exit(f"added vertex {f}: not a clean type on V° (matches {hits})")
            types.append(hits[0])
    counts = {"copy": sum(t < 20 for t in types), "const red": types.count(20),
              "const blue": types.count(21)}
    print("types:", counts)

    core = CERT + list(range(NV, n))
    rowR = [sum(O[core[i]][core[j]] << j for j in range(NCORE)) for i in range(NCORE)]
    full = (1 << NCORE) - 1
    rowB = [full ^ rowR[i] ^ (1 << i) for i in range(NCORE)]
    rowC = {1: rowR, 0: rowB}

    def vt(j):
        return types[j - 20]

    def is_nc(j):
        return j < 20 or vt(j) < 20

    def phi(j):
        return j if j < 20 else vt(j)

    def bit(x, i):
        return (x >> i) & 1

    cst = {c: sum(1 << j for j in range(20, NCORE) if vt(j) == (20 if c else 21)) for c in (1, 0)}
    bad = {}
    for c in (1, 0):
        rows = []
        for i in range(NCORE):
            r = 0
            for j in range(NCORE):
                if (i != j and is_nc(i) and is_nc(j) and bit(rowC[c][i], j)
                        and not bit(rowC[c][phi(i)], phi(j))):
                    r |= 1 << j
            rows.append(r)
        bad[c] = rows

    summary = {"graph_sha256": sha, "flips": args.flip, "types": types, "type_counts": counts}
    ok = True
    for c, name in ((1, "red"), (0, "blue")):
        rc, br, cm = rowC[c], bad[c], cst[c]
        counter = [0]
        f1 = no_clique(rc, 12, full, counter)
        h1 = all(rc[f] & cm == 0 for f in range(NCORE) if bit(cm, f))
        h2 = all(br[u] & rc[f] == 0 for f in range(NCORE) if bit(cm, f)
                 for u in range(NCORE) if bit(rc[f], u))
        h3 = all(br[u] & br[v] == 0 for u in range(NCORE) for v in range(NCORE) if bit(br[u], v))
        h4 = all(br[w] & (rc[u] & rc[v]) == 0 for u in range(NCORE) for v in range(NCORE)
                 if bit(br[u], v) for w in range(NCORE) if bit(rc[u] & rc[v], w))
        nbad = sum(bin(r).count("1") for r in br)
        res = {"noClique12": f1, "noClique_calls": counter[0], "h1": h1, "h2": h2, "h3": h3,
               "h4": h4, "conflict_ordered_pairs": nbad, "constant_vertices": bin(cm).count("1")}
        summary[name] = res
        print(f"[{name}] {res}")
        ok &= f1 and h1 and h2 and h3 and h4

    out = Path(args.out)
    src = f"""/-
R(12,12) ≥ 1658: generated by gen/gen_data.py from graph/r1212_1657.graph; do not edit by hand.
Source SHA-256: {sha}{'' if not args.flip else ' (with flips ' + ' '.join(args.flip) + ': NEGATIVE CONTROL)'}
-/
import RamseyIncrement.R1212.Search

/-!
# The 81-vertex core of the 1657-vertex colouring

Core positions: `0–9` are `c₀,…,c₉`, `10–19` are `i₀,…,i₉` (the certificates of
r1212-1642), and `20 + f` is added vertex `f` (file vertex `1596 + f`), `f < 61`.

`vt` and `rowR` take part in the definition of the colouring (`Graph.lean`).  The other
tables only speed up the checks; `Checks.lean` proves them equal to their definitions.
-/

namespace RamseyIncrement
namespace R1658

/-- The 81 core positions. -/
def mask81 : ℕ := 2 ^ 81 - 1

/-- Types of the added vertices, `5` bits each: `t < 20` is a copy of core vertex `t`,
`20` is constant red, `21` constant blue (towards `V°`). -/
def vtLit : ℕ := {lean_hex(types, 5)}

def vt (f : ℕ) : ℕ := (vtLit >>> (5 * f)) &&& 31

/-- Red rows of the core, `81` bits each: bit `j` of `rowR i` is set iff core vertices
`i` and `j` are joined by a red edge. -/
def rowRLit : ℕ := {lean_hex(rowR, NCORE)}

def rowR (i : ℕ) : ℕ := (rowRLit >>> (81 * i)) &&& mask81

/-- Constant-red core positions. -/
def cstRLit : ℕ := {hex(cst[1])}

/-- Constant-blue core positions. -/
def cstBLit : ℕ := {hex(cst[0])}

/-- Red conflict rows, `81` bits each. -/
def badRLit : ℕ := {lean_hex(bad[1], NCORE)}

/-- Blue conflict rows, `81` bits each. -/
def badBLit : ℕ := {lean_hex(bad[0], NCORE)}

end R1658
end RamseyIncrement
"""
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_bytes(src.encode("utf-8"))
    summary["output"] = str(out)
    summary["output_sha256"] = hashlib.sha256(src.encode("utf-8")).hexdigest()
    summary["all_checks_pass"] = bool(ok)
    print("wrote", out, summary["output_sha256"])
    if args.summary:
        Path(args.summary).write_text(json.dumps(summary, indent=1) + "\n", encoding="utf-8")
    print("CHECKS:", "PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
