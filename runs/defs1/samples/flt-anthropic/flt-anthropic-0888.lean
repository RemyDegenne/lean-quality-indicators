namespace P2MW.S_AutomorphicForm_exists_integral_baseChange_eq_mul_integral_mul_prod_integral_semiLocalHaar_of_isHaarMeasure

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set Filter

open NumberField.AdelicLevel TensorProduct

open scoped TensorProduct.RightActions NNReal ENNReal

noncomputable section

namespace AutomorphicForm

namespace SemiLocalGL2HaarFactor

p2m_open

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

section Kernel

variable (L) in

def kerSet : Set (Gad L) :=
  {k | glArch (𝓞 L) L k = 1 ∧ (∀ v ∈ S, cpt v k = 1) ∧ ∀ v, cpt v k ∈ semiLocalIntegralSet K L v}

end Kernel
end SemiLocalGL2HaarFactor
end AutomorphicForm
end
end P2MW.S_AutomorphicForm_exists_integral_baseChange_eq_mul_integral_mul_prod_integral_semiLocalHaar_of_isHaarMeasure
