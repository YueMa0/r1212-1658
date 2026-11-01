/-
R(12,12) ≥ 1658: the finite checks on the 81-vertex core, evaluated by the kernel.
-/
import RamseyIncrement.R1658.Data

/-!
# Finite checks on the core

Colour `c = true` is red, `c = false` is blue.  For a core position `j < 81`:

* `rowC c j`: the `c`-neighbours of `j` in the core;
* `cstMask c`: the added vertices that are constant `c` towards `V°`;
* `phi j`: the certificate vertex that `j` stands for on `V°` (`j` itself, or the vertex it
  copies);
* `badRow c i`: the conflicts of `i`, i.e. the `c`-neighbours `j` such that `phi i`, `phi j`
  are equal or not `c`-adjacent, with `i` and `j` both not constant.

`noK12` says that the core has no monochromatic `K₁₂`.  The four checks `check1`–`check4`
say that a `c`-clique of the core never contains two "defects"; `Defect.lean` turns this into
"deleting one vertex leaves no defect".
-/

namespace RamseyIncrement
namespace R1658

/-- Blue rows of the core: the complement of the red rows. -/
def rowB (i : ℕ) : ℕ := mask81 ^^^ rowR i ^^^ 2 ^ i

/-- The `c`-rows: red for `true`, blue for `false`. -/
def rowC : Bool → ℕ → ℕ
  | true => rowR
  | false => rowB

/-- The type code of a constant-`c` vertex. -/
def constCode : Bool → ℕ
  | true => 20
  | false => 21

/-- The constant-`c` core positions. -/
def cstMask : Bool → ℕ
  | true => cstRLit
  | false => cstBLit

/-- The conflict rows. -/
def badRow : Bool → ℕ → ℕ
  | true, i => (badRLit >>> (81 * i)) &&& mask81
  | false, i => (badBLit >>> (81 * i)) &&& mask81

/-- `j` is not constant: a certificate vertex or a copy. -/
def isNC (j : ℕ) : Bool := decide (j < 20) || decide (vt (j - 20) < 20)

/-- The certificate vertex that core position `j` stands for on `V°`. -/
def phi (j : ℕ) : ℕ := if j < 20 then j else vt (j - 20)

/-- The definition of a conflict. -/
def badB (c : Bool) (i j : ℕ) : Bool :=
  i != j && isNC i && isNC j && (rowC c i).testBit j && !(rowC c (phi i)).testBit (phi j)

/-- `p i` for all `i < n`. -/
def allLt (n : ℕ) (p : ℕ → Bool) : Bool := (List.range n).all p

/-- No two constant-`c` vertices are `c`-adjacent. -/
def check1 (c : Bool) : Bool :=
  allLt 81 fun f => !(cstMask c).testBit f || (rowC c f &&& cstMask c == 0)

/-- No conflict among the `c`-neighbours of a constant-`c` vertex. -/
def check2 (c : Bool) : Bool :=
  allLt 81 fun f => !(cstMask c).testBit f ||
    allLt 81 fun u => !(rowC c f).testBit u || (badRow c u &&& rowC c f == 0)

/-- No conflict triangle. -/
def check3 (c : Bool) : Bool :=
  allLt 81 fun u => allLt 81 fun v => !(badRow c u).testBit v || (badRow c u &&& badRow c v == 0)

/-- No conflict inside the common `c`-neighbourhood of a conflict. -/
def check4 (c : Bool) : Bool :=
  allLt 81 fun u => allLt 81 fun v => !(badRow c u).testBit v ||
    allLt 81 fun w => !(rowC c u &&& rowC c v).testBit w ||
      (badRow c w &&& (rowC c u &&& rowC c v) == 0)

/-! ## Kernel computations -/

theorem rowR_symm : ∀ i < 81, ∀ j < 81, (rowR i).testBit j = (rowR j).testBit i := by
  decide +kernel

theorem rowR_irrefl : ∀ i < 81, (rowR i).testBit i = false := by decide +kernel

theorem mask81_testBit : ∀ j < 81, mask81.testBit j = true := by decide +kernel

theorem vt_lt : ∀ f < 61, vt f < 22 := by decide +kernel

theorem cstMask_spec : ∀ c : Bool, ∀ j < 81,
    (cstMask c).testBit j = (decide (20 ≤ j) && vt (j - 20) == constCode c) := by
  decide +kernel

theorem badRow_spec : ∀ c : Bool, ∀ i < 81, ∀ j < 81, (badRow c i).testBit j = badB c i j := by
  decide +kernel

theorem badRow_symm : ∀ c : Bool, ∀ i < 81, ∀ j < 81,
    (badRow c i).testBit j = (badRow c j).testBit i := by
  decide +kernel

/-- **The core has no monochromatic `K₁₂`.** -/
theorem noK12 : ∀ c : Bool, R1212.Search.noClique (rowC c) 12 mask81 = true := by
  decide +kernel

theorem checks_ok : ∀ c : Bool, (check1 c && check2 c && check3 c && check4 c) = true := by
  decide +kernel

/-! ## Reading the checks -/

theorem allLt_spec {n : ℕ} {p : ℕ → Bool} (h : allLt n p = true) {i : ℕ} (hi : i < n) :
    p i = true :=
  List.all_eq_true.1 h i (List.mem_range.2 hi)

theorem testBit_eq_false_of_and {a b i : ℕ} (h : (a &&& b == 0) = true)
    (hb : b.testBit i = true) : a.testBit i = false := by
  have h0 : a &&& b = 0 := by simpa using h
  have := congrArg (fun x ↦ x.testBit i) h0
  simpa [Nat.testBit_and, hb] using this

variable {c : Bool}

theorem check1_ok (c : Bool) : check1 c = true := by
  have := checks_ok c
  simp only [Bool.and_eq_true] at this
  exact this.1.1.1

theorem check2_ok (c : Bool) : check2 c = true := by
  have := checks_ok c
  simp only [Bool.and_eq_true] at this
  exact this.1.1.2

theorem check3_ok (c : Bool) : check3 c = true := by
  have := checks_ok c
  simp only [Bool.and_eq_true] at this
  exact this.1.2

theorem check4_ok (c : Bool) : check4 c = true := by
  have := checks_ok c
  simp only [Bool.and_eq_true] at this
  exact this.2

theorem h1_of {f g : ℕ} (hf : f < 81) (hcf : (cstMask c).testBit f = true)
    (hfg : (rowC c f).testBit g = true) : (cstMask c).testBit g = false := by
  have h := allLt_spec (check1_ok c) hf
  simp only [hcf, Bool.not_true, Bool.false_or] at h
  have h0 : rowC c f &&& cstMask c = 0 := by simpa using h
  have := congrArg (fun x ↦ x.testBit g) h0
  simpa [Nat.testBit_and, hfg] using this

theorem h2_of {f u v : ℕ} (hf : f < 81) (hu : u < 81) (hcf : (cstMask c).testBit f = true)
    (hfu : (rowC c f).testBit u = true) (hfv : (rowC c f).testBit v = true) :
    (badRow c u).testBit v = false := by
  have h := allLt_spec (check2_ok c) hf
  simp only [hcf, Bool.not_true, Bool.false_or] at h
  have h' := allLt_spec h hu
  simp only [hfu, Bool.not_true, Bool.false_or] at h'
  exact testBit_eq_false_of_and h' hfv

theorem h3_of {u v w : ℕ} (hu : u < 81) (hv : v < 81) (huv : (badRow c u).testBit v = true)
    (hvw : (badRow c v).testBit w = true) : (badRow c u).testBit w = false := by
  have h := allLt_spec (allLt_spec (check3_ok c) hu) hv
  simp only [huv, Bool.not_true, Bool.false_or] at h
  exact testBit_eq_false_of_and h hvw

theorem h4_of {u v w x : ℕ} (hu : u < 81) (hv : v < 81) (hw : w < 81)
    (huv : (badRow c u).testBit v = true)
    (huw : (rowC c u).testBit w = true) (hvw : (rowC c v).testBit w = true)
    (hux : (rowC c u).testBit x = true) (hvx : (rowC c v).testBit x = true) :
    (badRow c w).testBit x = false := by
  have h := allLt_spec (allLt_spec (check4_ok c) hu) hv
  simp only [huv, Bool.not_true, Bool.false_or] at h
  have h' := allLt_spec h hw
  simp only [Nat.testBit_and, huw, hvw, Bool.and_self, Bool.not_true, Bool.false_or] at h'
  apply testBit_eq_false_of_and h'
  simp [Nat.testBit_and, hux, hvx]

/-! ## The colour rows -/

theorem rowB_testBit {i j : ℕ} (hj : j < 81) (hij : i ≠ j) :
    (rowB i).testBit j = !(rowR i).testBit j := by
  simp [rowB, Nat.testBit_xor, mask81_testBit j hj, R1212.Search.testBit_two_pow_ne hij]

/-- Off the diagonal, `rowC c` is red for `c = true` and not red for `c = false`. -/
theorem rowC_testBit (c : Bool) {i j : ℕ} (hj : j < 81) (hij : i ≠ j) :
    (rowC c i).testBit j = true ↔ ((rowR i).testBit j = true ↔ c = true) := by
  cases c
  · simp [rowC, rowB_testBit hj hij]
  · simp [rowC]

theorem rowC_irrefl (c : Bool) {i : ℕ} (hi : i < 81) : (rowC c i).testBit i = false := by
  cases c
  · simp [rowC, rowB, Nat.testBit_xor, mask81_testBit i hi, rowR_irrefl i hi]
  · exact rowR_irrefl i hi

theorem rowC_symm (c : Bool) {i j : ℕ} (hi : i < 81) (hj : j < 81) :
    (rowC c i).testBit j = (rowC c j).testBit i := by
  by_cases hij : i = j
  · rw [hij]
  cases c
  · simp only [rowC]
    rw [rowB_testBit hj hij, rowB_testBit hi (Ne.symm hij), rowR_symm i hi j hj]
  · exact rowR_symm i hi j hj

end R1658
end RamseyIncrement
