@[expose] public section

open MeasureTheory Set

open scoped Pointwise

namespace Grunbaum

/-- The part of `C` cut out by the sublevel halfspace of `ℓ` at `t`. -/
def trunc {d : ℕ} (C : Set (Euc d)) (ℓ : Euc d →L[ℝ] ℝ) (t : ℝ) : Set (Euc d) :=
  C ∩ ℓ ⁻¹' Set.Iic t

end Grunbaum
end
