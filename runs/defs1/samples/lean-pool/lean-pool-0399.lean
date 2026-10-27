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

private noncomputable local instance simplexBasisIndex_countable (n : ℕ) :
    Countable (simplexBasisIndex n) := by
  exact countable_hilbertBasis_index (simplexBasis n)

private noncomputable local instance globalBasisIndex_infinite :
    Infinite (Σ n : ℕ, simplexBasisIndex n) :=
  Infinite.of_injective globalBasisIndexPoint globalBasisIndexPoint_injective

/-- The constant-one vector in `L²(P)` for the probability measure supplied by `hB`. -/
noncomputable def probabilityOne (hB : IsPreBrownianReal B P) : RandomL2 P := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  exact indicatorConstLp 2 MeasurableSet.univ (measure_ne_top P Set.univ) (1 : ℝ)

end IteratedIntegralConstruction
end ContinuousTower
end Malliavin
end
