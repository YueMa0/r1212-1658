/-
R(12,12) ≥ 1658.
-/
import RamseyIncrement.R1658.Projection
import RamseyIncrement.RamseyNumber

/-!
# `R(12,12) ≥ 1658`

`G1657` (`Graph.lean`) is a red/blue colouring of `K₁₆₅₇`: the Mathon graph `M(797)` and 61
added vertices, each of which copies a certificate vertex of r1212-1642 or is constant towards
the rest of `M(797)`.  `Projection.lean` shows that it has no monochromatic `K₁₂`, using only
that `M(797)` is an `(11,11)`-colouring (`R1212.mathon_isRamseyFree`) and finite checks on the
81-vertex core (`Checks.lean`, evaluated by the kernel).
-/

namespace RamseyIncrement
namespace R1658

/-- A `(12,12)`-colouring on `1657` vertices. -/
theorem r1212_hasRamseyColoring : HasRamseyColoring 1657 12 12 :=
  ⟨_, G1657_isRamseyFree.overFin card_W⟩

/-- **`R(12,12) ≥ 1658`.** -/
theorem r1212_lower_bound : 1658 ≤ ramseyNumber 12 12 :=
  ramseyNumber_lower_bound r1212_hasRamseyColoring

end R1658
end RamseyIncrement
