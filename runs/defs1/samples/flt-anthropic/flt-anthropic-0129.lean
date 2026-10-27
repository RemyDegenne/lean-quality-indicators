namespace P2MW.S_AutomorphicForm_exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set Filter

open NumberField.AdelicLevel TensorProduct

open scoped TensorProduct.RightActions NNReal ENNReal

noncomputable section

namespace AutomorphicForm

namespace TwistedCentralizerHaarFactor

p2m_open

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

abbrev Gsl (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : Type :=
  GL (Fin 2) (SL K L v)

end TwistedCentralizerHaarFactor
end AutomorphicForm
end
end P2MW.S_AutomorphicForm_exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure
