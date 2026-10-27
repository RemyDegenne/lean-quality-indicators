namespace P2MW.S_AutomorphicForm_eq_ite_sum_of_isWeightedOrbitalIntegral_indicator_localIntegralSet_diagUnits2

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open MeasureTheory NumberField IsDedekindDomain TopologicalSpace Filter Set

open scoped NNReal ENNReal

open LanglandsTunnell.CubicInduction (diagUnits2)

noncomputable section

namespace P2mUnitWeightK

open AutomorphicForm

section Residue

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

abbrev kv : Type := IsLocalRing.ResidueField (v.adicCompletionIntegers K)

end Residue
end P2mUnitWeightK
end
end P2MW.S_AutomorphicForm_eq_ite_sum_of_isWeightedOrbitalIntegral_indicator_localIntegralSet_diagUnits2
