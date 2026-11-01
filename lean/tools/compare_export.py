"""Compare the Lean definition of the colouring with the published file.

    python -B tools/compare_export.py GRAPH [--summary PATH]

1. Rebuild the whole colouring from RamseyIncrement/R1658/Data.lean (its literals parsed
   here, not taken from gen_data.py), following Graph.lean case by case, and compare every
   byte with GRAPH.
2. Compare the rows that Export.lean wrote with Lean's interpreter
   (build/export/core_rows_from_lean.txt, rows `i:bits`) with the same rows of GRAPH.
3. If present, compare the earlier full-export attempt (build/export/r1212_1657_from_lean.graph,
   a prefix) with GRAPH.
"""
import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
P = 797
CERT = [930, 926, 1573, 1338, 1479, 1483, 1492, 1582, 1586, 1595,
        1061, 1588, 1576, 1549, 1554, 1594, 1472, 1557, 1079, 1267]  # Graph.lean `cert`


def lit(src, name):
    return int(re.search(rf"def {name} : ℕ := (0x[0-9a-f]+)", src).group(1), 16)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("graph")
    ap.add_argument("--summary", default=None)
    args = ap.parse_args()
    raw = Path(args.graph).read_bytes()
    rows = raw.split(b"\n")[:-1]
    n = len(rows)
    out = {"graph_sha256": hashlib.sha256(raw).hexdigest()}

    # 1. rebuild from Data.lean, following Graph.lean
    src = (ROOT / "RamseyIncrement" / "R1658" / "Data.lean").read_text(encoding="utf-8")
    out["data_lean_sha256"] = hashlib.sha256(src.encode("utf-8")).hexdigest()
    vt_lit, row_lit = lit(src, "vtLit"), lit(src, "rowRLit")
    vt = [(vt_lit >> (5 * f)) & 31 for f in range(61)]
    rowR = [(row_lit >> (81 * i)) & ((1 << 81) - 1) for i in range(81)]
    sq = {x * x % P for x in range(1, P)}

    def mv(v):  # file vertex -> M(797) vertex
        return ("A", v) if v < 797 else ("B", v - 797) if v < 1594 else ("a",) if v == 1594 else ("b",)

    def mathon(u, v):  # Mathon.lean `mathonAdj`
        if u == v:
            return 0
        ku, kv = u[0], v[0]
        if ku in "AB" and kv in "AB":
            d = (u[1] - v[1]) % P
            if ku == kv:
                return int(d in sq)
            return int(d != 0 and d not in sq)
        return int({ku, kv} in ({"A", "a"}, {"B", "b"}))

    cert_idx = {v: j for j, v in enumerate(CERT)}

    def adj(x, y):
        if x < 1596 and y < 1596:
            return mathon(mv(x), mv(y))
        if x >= 1596 and y >= 1596:  # adjW (inr f) (inr g)
            f, g = x - 1596, y - 1596
            return int(f != g and (rowR[20 + f] >> (20 + g)) & 1)
        u, f = (x, y - 1596) if x < 1596 else (y, x - 1596)  # crossAdj u f
        if u in cert_idx:
            return (rowR[cert_idx[u]] >> (20 + f)) & 1
        t = vt[f]  # typeAdj
        return mathon(mv(CERT[t]), mv(u)) if t < 20 else int(t == 20)

    bad = []
    for i in range(n):
        rebuilt = bytes(48 + adj(i, j) for j in range(n))
        if rebuilt != rows[i]:
            j = next(k for k in range(n) if rebuilt[k] != rows[i][k])
            bad.append((i, j))
            if len(bad) >= 5:
                break
    out["rebuild_from_data_lean"] = {"pairs": n * n, "first_differences": bad,
                                     "identical": not bad}
    print("rebuild from Data.lean:", "IDENTICAL" if not bad else f"DIFFERS at {bad}")

    # 2. rows evaluated by Lean's interpreter
    core = ROOT / "build" / "export" / "core_rows_from_lean.txt"
    if core.is_file():
        lines = core.read_bytes().split(b"\n")[:-1]
        ok, diff = 0, []
        for line in lines:
            i, bits = line.split(b":")
            i = int(i)
            if bits == rows[i]:
                ok += 1
            else:
                diff.append(i)
        out["lean_core_rows"] = {"file_sha256": hashlib.sha256(core.read_bytes()).hexdigest(),
                                 "rows": len(lines), "identical_rows": ok, "differing_rows": diff}
        print(f"Lean core rows: {ok}/{len(lines)} identical; differing {diff}")

    # 3. earlier prefix of a full export
    prefix = ROOT / "build" / "export" / "r1212_1657_from_lean.graph"
    if prefix.is_file():
        p = prefix.read_bytes()
        out["lean_full_export_prefix"] = {"bytes": len(p), "complete_rows": p.count(b"\n"),
                                          "identical": raw[:len(p)] == p}
        print(f"Lean full-export prefix: {len(p)} bytes, {p.count(b'\n')} rows,",
              "IDENTICAL" if raw[:len(p)] == p else "DIFFERS")
    if args.summary:
        Path(args.summary).write_text(json.dumps(out, indent=1) + "\n", encoding="utf-8")
    good = out["rebuild_from_data_lean"]["identical"] and not out.get(
        "lean_core_rows", {}).get("differing_rows")
    sys.exit(0 if good else 1)


if __name__ == "__main__":
    main()
