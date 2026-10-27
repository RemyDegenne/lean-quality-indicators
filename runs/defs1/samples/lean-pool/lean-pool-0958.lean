@[expose] public section

namespace Malliavin

open MeasureTheory

open scoped NNReal

universe u_1 u_2 u_3 u_4 u_7 u_8

universe u₁ u₂ u₃ u₄ u₅

variable {Ω : Type*} [MeasureSpace Ω]

section ContinuousTower

open ProbabilityTheory

open scoped ENNReal NNReal InnerProductSpace lp

variable {Ω' : Type*} [mΩ' : MeasurableSpace Ω'] {P : Measure Ω'}
  {B : ℝ≥0 → Ω' → ℝ}

namespace IteratedIntegralConstruction

local instance fact_two_ne_top : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

/-- A chosen Hilbert basis of a positive-order simplex-kernel space. -/
noncomputable def simplexBasis (n : ℕ) :
    HilbertBasis (simplexBasisIndex n) ℝ (SimplexKernel (n + 1)) :=
  Classical.choose (show ∃ b : HilbertBasis (simplexBasisIndex n) ℝ
      (SimplexKernel (n + 1)), ⇑b = Subtype.val from
    Classical.choose_spec (exists_hilbertBasis ℝ (SimplexKernel (n + 1))))

end IteratedIntegralConstruction
end ContinuousTower
end Malliavin
end
