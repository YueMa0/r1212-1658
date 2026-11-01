/-
R(12,12) ≥ 1658: the 1657-vertex colouring.
-/
import RamseyIncrement.R1212.Mathon
import RamseyIncrement.R1658.Checks

/-!
# The colouring on `M(797) ⊕ Fin 61`

The vertices are `inl u` for `u` in the Mathon graph `M(797)` (file vertices `0–1595`, in the
order of r1212-1642) and `inr f` for `f < 61` (file vertex `1596 + f`).  Red edges:

* `inl u`, `inl v`: as in `M(797)`;
* `inl u`, `inr f`: if `u` is one of the 20 certificate vertices, as in the core table
  `rowR`; otherwise as given by the type `vt f` of `f`: a copy of certificate vertex `t`
  (`vt f = t < 20`) is red to `u` iff `t` is, a constant vertex is red (`vt f = 20`) or blue
  (`vt f = 21`) to all of `V°`;
* `inr f`, `inr g`: as in the core table.

`Export.lean` writes this colouring out; it is byte-for-byte the published file.
-/

namespace RamseyIncrement
namespace R1658

open R1212 R1212.MV

/-- The certificates of r1212-1642: `c₀,…,c₉` (a red `K₁₀`), then `i₀,…,i₉` (a blue `K₁₀`).
File vertices `930, 926, 1573, 1338, 1479, 1483, 1492, 1582, 1586, 1595` and
`1061, 1588, 1576, 1549, 1554, 1594, 1472, 1557, 1079, 1267`. -/
def cert : Fin 20 → MV :=
  ![B 133, B 129, B 776, B 541, B 682, B 686, B 695, B 785, B 789, b,
    B 264, B 791, B 779, B 752, B 757, a, B 675, B 760, B 282, B 470]

theorem cert_injective : Function.Injective cert := by decide +kernel

/-- `cert n` for `n < 20` (`b` otherwise; never used). -/
def certN (n : ℕ) : MV := if h : n < 20 then cert ⟨n, h⟩ else b

theorem certN_lt {n : ℕ} (h : n < 20) : certN n = cert ⟨n, h⟩ := dif_pos h

theorem certN_inj {p q : ℕ} (hp : p < 20) (hq : q < 20) (h : certN p = certN q) : p = q := by
  rw [certN_lt hp, certN_lt hq] at h
  exact Fin.mk.inj_iff.1 (cert_injective h)

/-- The position of `u` among the certificate vertices. -/
def certIdx (u : MV) : Option (Fin 20) := (List.finRange 20).find? fun j ↦ decide (cert j = u)

theorem certIdx_cert : ∀ j : Fin 20, certIdx (cert j) = some j := by decide +kernel

theorem cert_of_certIdx {u : MV} {j : Fin 20} (h : certIdx u = some j) : cert j = u := by
  have h' : (List.finRange 20).find? (fun k ↦ decide (cert k = u)) = some j := h
  have h'' := List.find?_some h'
  simpa using h''

theorem certIdx_certN {p : ℕ} (hp : p < 20) : certIdx (certN p) = some ⟨p, hp⟩ := by
  rw [certN_lt hp, certIdx_cert]

theorem certN_ne_of_none {p : ℕ} (hp : p < 20) {u : MV} (hu : certIdx u = none) :
    certN p ≠ u := by
  rintro rfl
  rw [certIdx_certN hp] at hu
  exact Option.some_ne_none _ hu

/-- Red edges between an added vertex of type `t` and a vertex `u` of `V°`. -/
def typeAdj (t : ℕ) (u : MV) : Prop := if t < 20 then mathon.Adj (certN t) u else t = 20

instance (t : ℕ) (u : MV) : Decidable (typeAdj t u) :=
  if h : t < 20 then decidable_of_iff (mathon.Adj (certN t) u) (by simp [typeAdj, h])
  else decidable_of_iff (t = 20) (by simp [typeAdj, h])

/-- Red edges between `u ∈ M(797)` and added vertex `f`. -/
def crossAdj (u : MV) (f : Fin 61) : Prop :=
  match certIdx u with
  | some j => (rowR j).testBit (20 + f.val) = true
  | none => typeAdj (vt f) u

instance (u : MV) (f : Fin 61) : Decidable (crossAdj u f) :=
  match h : certIdx u with
  | some j => decidable_of_iff ((rowR j).testBit (20 + f.val) = true) (by simp [crossAdj, h])
  | none => decidable_of_iff (typeAdj (vt f) u) (by simp [crossAdj, h])

/-- The vertices: `M(797)`, then the 61 added vertices. -/
abbrev W := MV ⊕ Fin 61

/-- The red relation. -/
def adjW : W → W → Prop
  | .inl u, .inl v => mathon.Adj u v
  | .inl u, .inr f => crossAdj u f
  | .inr f, .inl u => crossAdj u f
  | .inr f, .inr g => f ≠ g ∧ (rowR (20 + f.val)).testBit (20 + g.val) = true

/-- The 1657-vertex colouring; red edges are graph edges. -/
def G1657 : SimpleGraph W where
  Adj := adjW
  symm := ⟨fun x y h ↦ by
    rcases x with u | f <;> rcases y with v | g
    · exact SimpleGraph.Adj.symm (G := mathon) h
    · exact h
    · exact h
    · obtain ⟨hfg, hb⟩ := h
      have hf : 20 + f.val < 81 := by have := f.isLt; omega
      have hg : 20 + g.val < 81 := by have := g.isLt; omega
      show g ≠ f ∧ (rowR (20 + g.val)).testBit (20 + f.val) = true
      exact ⟨Ne.symm hfg, (rowR_symm _ hg _ hf).trans hb⟩⟩
  loopless := ⟨fun x h ↦ by
    rcases x with u | f
    · exact mathon.loopless.irrefl u h
    · obtain ⟨hff, -⟩ := h
      exact hff rfl⟩

instance : DecidableRel G1657.Adj := fun x y ↦
  match x, y with
  | .inl u, .inl v => mathonDecAdj u v
  | .inl u, .inr f => (inferInstance : Decidable (crossAdj u f))
  | .inr f, .inl u => (inferInstance : Decidable (crossAdj u f))
  | .inr f, .inr g =>
      (inferInstance : Decidable (f ≠ g ∧ (rowR (20 + f.val)).testBit (20 + g.val) = true))

theorem card_W : Fintype.card W = 1657 := by
  rw [Fintype.card_sum, card_MV, Fintype.card_fin]

/-! ## The definition, read back -/

/-- `M(797)` is an induced subgraph. -/
theorem adj_inl_inl (u v : MV) : G1657.Adj (.inl u) (.inl v) ↔ mathon.Adj u v := Iff.rfl

/-- An added vertex that copies certificate vertex `t` has its colour towards `V°`. -/
theorem adj_inr_copy {f : Fin 61} {t : ℕ} (ht : vt f = t) (h20 : t < 20) {u : MV}
    (hu : certIdx u = none) : G1657.Adj (.inr f) (.inl u) ↔ mathon.Adj (certN t) u := by
  show crossAdj u f ↔ _
  simp [crossAdj, hu, typeAdj, ht, h20]

/-- Constant vertices towards `V°`. -/
theorem adj_inr_const {f : Fin 61} (c : Bool) (ht : vt f = constCode c) {u : MV}
    (hu : certIdx u = none) : G1657.Adj (.inr f) (.inl u) ↔ c = true := by
  show crossAdj u f ↔ _
  cases c <;> simp [crossAdj, hu, typeAdj, ht, constCode]

/-- The core table agrees with `M(797)` on the certificates. -/
theorem rowR_cert : ∀ p < 20, ∀ q < 20,
    (rowR p).testBit q = decide (mathon.Adj (certN p) (certN q)) := by
  decide +kernel

/-! ## Core positions -/

/-- Core position `j < 81` as a vertex: `cert j` for `j < 20`, added vertex `j - 20` otherwise. -/
def coreV (j : ℕ) : W :=
  if j < 20 then .inl (certN j) else .inr ⟨(j - 20) % 61, Nat.mod_lt _ (by norm_num)⟩

/-- The core position of a vertex; `81` for the vertices of `V°`. -/
def idx : W → ℕ
  | .inl u =>
    match certIdx u with
    | some j => j.val
    | none => 81
  | .inr f => 20 + f.val

theorem coreV_lt {j : ℕ} (h : j < 20) : coreV j = .inl (certN j) := if_pos h

theorem coreV_add (f : Fin 61) : coreV (20 + f.val) = .inr f := by
  rw [coreV, if_neg (by omega)]
  apply congrArg Sum.inr
  apply Fin.ext
  show (20 + f.val - 20) % 61 = f.val
  rw [Nat.add_sub_cancel_left]
  exact Nat.mod_eq_of_lt f.isLt

theorem idx_inl_some {u : MV} {j : Fin 20} (h : certIdx u = some j) :
    idx (.inl u) = j.val := by
  simp [idx, h]

theorem idx_inl_none {u : MV} (h : certIdx u = none) : idx (.inl u) = 81 := by
  simp [idx, h]

theorem coreV_idx {x : W} (hx : idx x < 81) : coreV (idx x) = x := by
  rcases x with u | f
  · cases h : certIdx u with
    | none =>
      rw [idx_inl_none h] at hx
      exact absurd hx (lt_irrefl 81)
    | some j =>
      rw [idx_inl_some h, coreV_lt j.isLt, certN_lt j.isLt, cert_of_certIdx h]
  · exact coreV_add f

theorem eq_inl_of_idx {x : W} (hx : ¬idx x < 81) : ∃ u, x = .inl u ∧ certIdx u = none := by
  rcases x with u | f
  · cases h : certIdx u with
    | none => exact ⟨u, rfl, h⟩
    | some j =>
      rw [idx_inl_some h] at hx
      exact absurd (by have := j.isLt; omega) hx
  · exfalso
    apply hx
    show 20 + f.val < 81
    have := f.isLt
    omega

theorem exists_fin_of_ge {j : ℕ} (hj : j < 81) (h20 : 20 ≤ j) : ∃ f : Fin 61, j = 20 + f.val :=
  ⟨⟨j - 20, by omega⟩, show j = 20 + (j - 20) by omega⟩

/-- Between core positions, the colouring is the core table. -/
theorem adj_core {i j : ℕ} (hi : i < 81) (hj : j < 81) (hij : i ≠ j) :
    G1657.Adj (coreV i) (coreV j) ↔ (rowR i).testBit j = true := by
  rcases lt_or_ge i 20 with hi20 | hi20 <;> rcases lt_or_ge j 20 with hj20 | hj20
  · rw [coreV_lt hi20, coreV_lt hj20, adj_inl_inl, rowR_cert i hi20 j hj20, decide_eq_true_iff]
  · obtain ⟨g, rfl⟩ := exists_fin_of_ge hj hj20
    rw [coreV_lt hi20, coreV_add g]
    show crossAdj (certN i) g ↔ _
    simp [crossAdj, certIdx_certN hi20]
  · obtain ⟨f, rfl⟩ := exists_fin_of_ge hi hi20
    rw [coreV_add f, coreV_lt hj20, rowR_symm _ hi _ hj]
    show crossAdj (certN j) f ↔ _
    simp [crossAdj, certIdx_certN hj20]
  · obtain ⟨f, rfl⟩ := exists_fin_of_ge hi hi20
    obtain ⟨g, rfl⟩ := exists_fin_of_ge hj hj20
    rw [coreV_add f, coreV_add g]
    show f ≠ g ∧ _ ↔ _
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨fun e ↦ hij (by rw [e]), h⟩⟩

/-- Towards `V°`, a non-constant core position has the colour of the certificate vertex it
stands for. -/
theorem adj_out_nc {j : ℕ} (hj : j < 81) (hnc : isNC j = true) {u : MV}
    (hu : certIdx u = none) : G1657.Adj (coreV j) (.inl u) ↔ mathon.Adj (certN (phi j)) u := by
  rcases lt_or_ge j 20 with hj20 | hj20
  · rw [coreV_lt hj20, adj_inl_inl, phi, if_pos hj20]
  · obtain ⟨f, rfl⟩ := exists_fin_of_ge hj hj20
    have hnot : ¬20 + f.val < 20 := by omega
    have hvt : vt f.val < 20 := by
      simpa [isNC, hnot, Nat.add_sub_cancel_left] using hnc
    rw [coreV_add f, adj_inr_copy rfl hvt hu, phi, if_neg hnot, Nat.add_sub_cancel_left]

/-- Towards `V°`, a constant-`c'` core position has colour `c'`. -/
theorem adj_out_const {j : ℕ} (hj : j < 81) (hj20 : 20 ≤ j) (c' : Bool)
    (hc : vt (j - 20) = constCode c') {u : MV} (hu : certIdx u = none) :
    G1657.Adj (coreV j) (.inl u) ↔ c' = true := by
  obtain ⟨f, rfl⟩ := exists_fin_of_ge hj hj20
  rw [Nat.add_sub_cancel_left] at hc
  rw [coreV_add f, adj_inr_const c' hc hu]

end R1658
end RamseyIncrement
