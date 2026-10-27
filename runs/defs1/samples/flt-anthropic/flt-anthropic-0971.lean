namespace P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_subgroup_units_map_val_eq_withDensity_of_abs_det_eq

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

p2m_open

open scoped NNReal ENNReal Pointwise

noncomputable section

namespace MeasureTheory

namespace UnitGroupHaar

p2m_open

section Invariance

variable {M : Type*} [Ring M] [Algebra ℝ M] [FiniteDimensional ℝ M]
  [TopologicalSpace M] [IsTopologicalRing M] [ContinuousSMul ℝ M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M]
  {n : ℕ} (e : Fin n → M) (χ : M →* ℝ)

def ν : Measure M := (Measure.map (ψ e) volume).withDensity (dens χ)

end Invariance
end UnitGroupHaar
end MeasureTheory
end
end P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_subgroup_units_map_val_eq_withDensity_of_abs_det_eq
