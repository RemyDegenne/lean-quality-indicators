namespace P2MW.S_LanglandsTunnell_CubicInduction_integral_integral_diagUnits2_longWeyl3_upperUnipotent3_weylPrime3_eq_mul_of_central

set_option autoImplicit false

set_option maxHeartbeats 3200000

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

open MeasureTheory LanglandsTunnell.TateLocal

open scoped NNReal ENNReal Matrix

noncomputable section

namespace LTMiddleIdentity

open LanglandsTunnell.CubicInduction

section Weights

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]

theorem mC_nonneg (x : Kˣ) : (0 : ℝ) ≤ (modulus (x : K) : ℝ) := (mC_pos x).le

end Weights
end LTMiddleIdentity
end
end P2MW.S_LanglandsTunnell_CubicInduction_integral_integral_diagUnits2_longWeyl3_upperUnipotent3_weylPrime3_eq_mul_of_central
