namespace P2MW.S_AutomorphicForm_exists_integral_eq_mul_integral_mul_prod_integral_localHaar_of_isHaarMeasure

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set Filter

open NumberField.AdelicLevel

open scoped NNReal ENNReal

noncomputable section

namespace AutomorphicForm

namespace AdelicGL2HaarFactor

p2m_open

variable {K : Type} [Field K] [NumberField K]

abbrev SProd (S : Finset (HeightOneSpectrum (𝓞 K))) : Type := (v : S) → Gv (K := K) v.1

end AdelicGL2HaarFactor
end AutomorphicForm
end
end P2MW.S_AutomorphicForm_exists_integral_eq_mul_integral_mul_prod_integral_localHaar_of_isHaarMeasure
