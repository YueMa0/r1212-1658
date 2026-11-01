/-
R(12,12) ≥ 1658: the projection argument.
-/
import RamseyIncrement.R1658.Graph
import RamseyIncrement.R1658.Defect
import RamseyIncrement.R1212.PaleyClique

/-!
# No monochromatic `K₁₂`

Let `Q` be a clique of colour `c` with `12` vertices.  Its vertices are core vertices (the 20
certificate vertices and the 61 added vertices; their core positions form `K`) or vertices of
`V°`.

* If `K` contains a vertex that is constant `¬c` towards `V°`, then `Q` has no vertex in `V°`.
  So `K` is a `c`-clique of the core with `12` vertices, which `noK12` excludes.
* Otherwise `defect_le_one` gives `S ⊆ K` with `|S| ≥ |K| - 1`, no constant vertex and no
  conflict.  The certificate vertices `phi j` (`j ∈ S`) are then distinct and form a
  `c`-clique `T` of `M(797)`.  Each vertex of `Q` in `V°` has colour `c` towards each of them
  (copies copy).  So `T` and the part of `Q` in `V°` form a `c`-clique of `M(797)` with at least
  `|K| - 1 + (12 - |K|) = 11` vertices, which `mathon_isRamseyFree` excludes.

Only this last step uses anything about `M(797)` beyond the 20 certificate vertices.
-/

namespace RamseyIncrement
namespace R1658

open R1212 SimpleGraph

/-- `G` for red (`true`), `Gᶜ` for blue (`false`). -/
def colG {V : Type*} : Bool → SimpleGraph V → SimpleGraph V
  | true, G => G
  | false, G => Gᶜ

theorem colG_adj {V : Type*} (c : Bool) (G : SimpleGraph V) (x y : V) :
    (colG c G).Adj x y ↔ x ≠ y ∧ (G.Adj x y ↔ c = true) := by
  cases c
  · show Gᶜ.Adj x y ↔ _
    rw [compl_adj]
    simp
  · show G.Adj x y ↔ _
    exact ⟨fun h ↦ ⟨G.ne_of_adj h, iff_of_true h rfl⟩, fun h ↦ h.2.2 rfl⟩

theorem mathon_colG_cliqueFree (c : Bool) : (colG c mathon).CliqueFree 11 := by
  have h := mathon_isRamseyFree paley_cliqueFree
  cases c
  · exact h.2
  · exact h.1

/-- The vertex of `M(797)` under a vertex of `W` (`b` for the added vertices; never used). -/
def toMV : W → MV := Sum.elim id fun _ ↦ MV.b

/-- **No `c`-clique with `12` vertices.** -/
theorem colG_cliqueFree (c : Bool) : (colG c G1657).CliqueFree 12 := by
  classical
  intro Q hQ
  have hadj : ∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → (G1657.Adj x y ↔ c = true) := fun x hx y hy hxy ↦
    ((colG_adj c G1657 x y).1 (hQ.isClique hx hy hxy)).2
  -- the core part and the `V°` part of `Q`
  obtain ⟨Qc, hQc⟩ : ∃ Qc : Finset W, Qc = Q.filter (fun x ↦ idx x < 81) := ⟨_, rfl⟩
  obtain ⟨Qo, hQo⟩ : ∃ Qo : Finset W, Qo = Q.filter (fun x ↦ ¬idx x < 81) := ⟨_, rfl⟩
  have memQc : ∀ x, x ∈ Qc ↔ x ∈ Q ∧ idx x < 81 := fun x ↦ by rw [hQc, Finset.mem_filter]
  have memQo : ∀ x, x ∈ Qo ↔ x ∈ Q ∧ ¬idx x < 81 := fun x ↦ by rw [hQo, Finset.mem_filter]
  have hsplit : Qc.card + Qo.card = 12 := by
    rw [hQc, hQo, Finset.card_filter_add_card_filter_not, hQ.card_eq]
  -- the core positions `K` of `Q`
  obtain ⟨K, hK⟩ : ∃ K : Finset ℕ, K = Qc.image idx := ⟨_, rfl⟩
  have memK : ∀ j, j ∈ K ↔ ∃ x ∈ Qc, idx x = j := fun j ↦ by rw [hK, Finset.mem_image]
  have hKcard : K.card = Qc.card := by
    rw [hK]
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    have hx' := ((memQc x).1 hx).2
    have hy' := ((memQc y).1 hy).2
    calc x = coreV (idx x) := (coreV_idx hx').symm
      _ = coreV (idx y) := by rw [hxy]
      _ = y := coreV_idx hy'
  have hKlt : ∀ j ∈ K, j < 81 := by
    intro j hj
    obtain ⟨x, hx, rfl⟩ := (memK j).1 hj
    exact ((memQc x).1 hx).2
  have hKclique : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → (rowC c i).testBit j = true := by
    intro i hi j hj hij
    obtain ⟨x, hx, rfl⟩ := (memK i).1 hi
    obtain ⟨y, hy, rfl⟩ := (memK j).1 hj
    have hx' := (memQc x).1 hx
    have hy' := (memQc y).1 hy
    have hxy : x ≠ y := fun h ↦ hij (by rw [h])
    rw [rowC_testBit c hy'.2 hij, ← adj_core hx'.2 hy'.2 hij, coreV_idx hx'.2, coreV_idx hy'.2]
    exact hadj x hx'.1 y hy'.1 hxy
  by_cases hA : ∃ x ∈ Qc, 20 ≤ idx x ∧ vt (idx x - 20) = constCode (!c)
  · -- a constant-`¬c` vertex: `Q` lies in the core
    obtain ⟨x, hx, hx20, hxc⟩ := hA
    have hx' := (memQc x).1 hx
    have hQo0 : Qo = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro y hy
      have hy' := (memQo y).1 hy
      obtain ⟨u, rfl, hu⟩ := eq_inl_of_idx hy'.2
      have hxy : x ≠ .inl u := fun h ↦ hy'.2 (h ▸ hx'.2)
      have h1 := hadj x hx'.1 _ hy'.1 hxy
      rw [← coreV_idx hx'.2, adj_out_const hx'.2 hx20 (!c) hxc hu] at h1
      cases c <;> simp at h1
    rw [hQo0, Finset.card_empty] at hsplit
    have := R1212.Search.noClique_sound (rowC c) 12 mask81 (noK12 c) K hKclique
      (fun j hj ↦ mask81_testBit j (hKlt j hj))
    omega
  -- no constant-`¬c` vertex: delete at most one defect
  push Not at hA
  have hKnc : ∀ j ∈ K, 20 ≤ j → vt (j - 20) ≠ constCode (!c) := by
    intro j hj
    obtain ⟨x, hx, rfl⟩ := (memK j).1 hj
    exact hA x hx
  obtain ⟨S, hSK, hScard, hScst, hSbad⟩ := defect_le_one (n := 81)
    (adj := fun u v ↦ (rowC c u).testBit v = true)
    (cst := fun j ↦ (cstMask c).testBit j = true)
    (bad := fun u v ↦ (badRow c u).testBit v = true)
    (fun u hu v hv h ↦ by rw [← badRow_symm c u hu v hv]; exact h)
    (fun f hf g hcf hfg hcg ↦ Bool.false_ne_true ((h1_of hf hcf hfg).symm.trans hcg))
    (fun f hf u hu v hcf hfu hfv hb ↦
      Bool.false_ne_true ((h2_of hf hu hcf hfu hfv).symm.trans hb))
    (fun u hu v hv w huv hvw huw ↦ Bool.false_ne_true ((h3_of hu hv huv hvw).symm.trans huw))
    (fun u hu v hv w hw x huv huw hvw hux hvx hwx ↦
      Bool.false_ne_true ((h4_of hu hv hw huv huw hvw hux hvx).symm.trans hwx))
    K hKlt hKclique
  -- every position in `S` stands for a certificate vertex
  have hSnc : ∀ j ∈ S, isNC j = true ∧ phi j < 20 := by
    intro j hj
    have hjK := hSK hj
    have hj81 := hKlt j hjK
    have hcst : (cstMask c).testBit j = false := by simpa using hScst j hj
    rw [cstMask_spec c j hj81] at hcst
    rcases lt_or_ge j 20 with h20 | h20
    · exact ⟨by simp [isNC, h20], by simp [phi, h20]⟩
    · have hvt := vt_lt (j - 20) (by omega)
      have h1 : vt (j - 20) ≠ constCode c := by simpa [h20] using hcst
      have h2 := hKnc j hjK h20
      have hlt : vt (j - 20) < 20 := by
        cases c <;> simp only [constCode, Bool.not_true, Bool.not_false] at h1 h2 <;> omega
      exact ⟨by simp [isNC, hlt], by simp [phi, show ¬j < 20 by omega, hlt]⟩
  -- two positions of `S` stand for distinct certificate vertices joined in colour `c`
  have hSpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      phi i ≠ phi j ∧ (mathon.Adj (certN (phi i)) (certN (phi j)) ↔ c = true) := by
    intro i hi j hj hij
    have hi81 := hKlt i (hSK hi)
    have hj81 := hKlt j (hSK hj)
    have hcl := hKclique i (hSK hi) j (hSK hj) hij
    have hb : (badRow c i).testBit j = false := by simpa using hSbad i hi j hj hij
    rw [badRow_spec c i hi81 j hj81] at hb
    have hne : (i != j) = true := bne_iff_ne.2 hij
    have hb' : (rowC c (phi i)).testBit (phi j) = true := by
      simpa [badB, hne, (hSnc i hi).1, (hSnc j hj).1, hcl] using hb
    have hpi := (hSnc i hi).2
    have hpj := (hSnc j hj).2
    have hne' : phi i ≠ phi j := by
      intro h
      rw [h, rowC_irrefl c (by omega)] at hb'
      exact Bool.false_ne_true hb'
    refine ⟨hne', ?_⟩
    rw [← decide_eq_true_iff (p := mathon.Adj _ _), ← rowR_cert _ hpi _ hpj]
    exact (rowC_testBit c (by omega) hne').1 hb'
  -- `T`: those certificate vertices; `U`: the part of `Q` in `V°`
  obtain ⟨T, hT⟩ : ∃ T : Finset MV, T = S.image (fun j ↦ certN (phi j)) := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : Finset MV, U = Qo.image toMV := ⟨_, rfl⟩
  have memU : ∀ u ∈ U, certIdx u = none ∧ (.inl u : W) ∈ Q := by
    intro u hu
    rw [hU, Finset.mem_image] at hu
    obtain ⟨y, hy, rfl⟩ := hu
    have hy' := (memQo y).1 hy
    obtain ⟨v, rfl, hv⟩ := eq_inl_of_idx hy'.2
    exact ⟨hv, hy'.1⟩
  have hTcard : T.card = S.card := by
    rw [hT]
    apply Finset.card_image_of_injOn
    intro i hi j hj hij
    by_contra hne
    exact (hSpair i hi j hj hne).1 (certN_inj (hSnc i hi).2 (hSnc j hj).2 hij)
  have hUcard : U.card = Qo.card := by
    rw [hU]
    apply Finset.card_image_of_injOn
    intro y₁ hy₁ y₂ hy₂ h
    obtain ⟨u₁, rfl, -⟩ := eq_inl_of_idx ((memQo y₁).1 hy₁).2
    obtain ⟨u₂, rfl, -⟩ := eq_inl_of_idx ((memQo y₂).1 hy₂).2
    exact congrArg Sum.inl h
  have hdisj : Disjoint T U := by
    rw [Finset.disjoint_left]
    intro a haT haU
    rw [hT, Finset.mem_image] at haT
    obtain ⟨i, hi, rfl⟩ := haT
    exact certN_ne_of_none (hSnc i hi).2 (memU _ haU).1 rfl
  have hTT : ∀ a ∈ T, ∀ a' ∈ T, a ≠ a' → (colG c mathon).Adj a a' := by
    intro a ha a' ha' haa'
    rw [hT, Finset.mem_image] at ha ha'
    obtain ⟨i, hi, rfl⟩ := ha
    obtain ⟨j, hj, rfl⟩ := ha'
    have hij : i ≠ j := fun h ↦ haa' (by rw [h])
    rw [colG_adj]
    exact ⟨haa', (hSpair i hi j hj hij).2⟩
  have hTU : ∀ a ∈ T, ∀ u ∈ U, (colG c mathon).Adj a u := by
    intro a ha u hu
    rw [hT, Finset.mem_image] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    obtain ⟨hu0, huQ⟩ := memU u hu
    have hjK := hSK hj
    obtain ⟨x, hx, hxj⟩ := (memK j).1 hjK
    have hx' := (memQc x).1 hx
    have hxu : x ≠ .inl u := by
      rintro rfl
      rw [idx_inl_none hu0] at hx'
      exact lt_irrefl _ hx'.2
    have h1 := hadj x hx'.1 _ huQ hxu
    rw [← coreV_idx hx'.2, hxj, adj_out_nc (hKlt j hjK) (hSnc j hj).1 hu0] at h1
    rw [colG_adj]
    exact ⟨certN_ne_of_none (hSnc j hj).2 hu0, h1⟩
  have hUU : ∀ u ∈ U, ∀ u' ∈ U, u ≠ u' → (colG c mathon).Adj u u' := by
    intro u hu u' hu' huu'
    have h1 := hadj _ (memU u hu).2 _ (memU u' hu').2 (fun h ↦ huu' (Sum.inl_injective h))
    rw [colG_adj]
    exact ⟨huu', h1⟩
  -- together: a `c`-clique of `M(797)` with at least `11` vertices
  have hclique : (colG c mathon).IsClique ((T ∪ U : Finset MV) : Set MV) := by
    intro a ha a' ha' haa'
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at ha ha'
    rcases ha with ha | ha <;> rcases ha' with ha' | ha'
    · exact hTT a ha a' ha' haa'
    · exact hTU a ha a' ha'
    · exact (hTU a' ha' a ha).symm
    · exact hUU a ha a' ha' haa'
  have hcard : 11 ≤ (T ∪ U).card := by
    rw [Finset.card_union_of_disjoint hdisj, hTcard, hUcard]
    omega
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hcard
  exact mathon_colG_cliqueFree c t ⟨hclique.subset (Finset.coe_subset.2 hts), htc⟩

/-- **The 1657-vertex colouring has no monochromatic `K₁₂`.** -/
theorem G1657_isRamseyFree : IsRamseyFree G1657 12 12 :=
  ⟨colG_cliqueFree true, colG_cliqueFree false⟩

end R1658
end RamseyIncrement
