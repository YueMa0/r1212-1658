import RamseyIncrement.R1658.Graph

/-!
# Writing out the colouring

Not part of the proof.  Evaluates `G1657.Adj` (with Lean's interpreter) in the vertex order of
the published file and writes rows `i:` followed by 1657 characters, `1` for red.
`tools/compare_export.py` compares them with `graph/r1212_1657.graph`.

The interpreter takes about 8 s per row, so only the rows of the 81 core vertices (the 20
certificate vertices and the 61 added vertices) are written: every pair whose colour is not
simply that of `M(797)` lies in one of these rows.  Replace `coreRows` by `List.range 1657`
for the whole colouring (about 3.7 hours).
-/

open RamseyIncrement R1658 R1212

/-- File vertex `n`: `A_n`, `B_{n-797}`, `a`, `b`, then added vertex `n - 1596`. -/
def vertexOf (n : ℕ) : W :=
  if n < 797 then .inl (MV.A (n : ZMod 797))
  else if n < 1594 then .inl (MV.B ((n - 797 : ℕ) : ZMod 797))
  else if n = 1594 then .inl MV.a
  else if n = 1595 then .inl MV.b
  else .inr ⟨(n - 1596) % 61, Nat.mod_lt _ (by norm_num)⟩

def exportRow (i : ℕ) : String :=
  String.mk ((List.range 1657).map fun j ↦
    if decide (G1657.Adj (vertexOf i) (vertexOf j)) then '1' else '0')

/-- File vertices of `c₀,…,c₉`, `i₀,…,i₉`, then the 61 added vertices. -/
def coreRows : List ℕ :=
  [930, 926, 1573, 1338, 1479, 1483, 1492, 1582, 1586, 1595,
    1061, 1588, 1576, 1549, 1554, 1594, 1472, 1557, 1079, 1267] ++
  (List.range 61).map (· + 1596)

#eval show IO Unit from do
  IO.FS.createDirAll "build/export"
  let h ← IO.FS.Handle.mk "build/export/core_rows_from_lean.txt" IO.FS.Mode.write
  for i in coreRows do
    h.putStr (toString i ++ ":" ++ exportRow i ++ "\n")
    h.flush
  IO.println "wrote build/export/core_rows_from_lean.txt"
