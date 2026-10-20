namespace P2MW.S_AutomorphicForm_exists_isTwistedWeightedOrbitalIntegralOn_baseChange_eq_mul_sum_prod_of_isSemiLocalFactorization

attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set Filter

open NumberField.AdelicLevel NumberField.AdelicHaar TensorProduct

open scoped TensorProduct.RightActions NNReal ENNReal Pointwise Classical

noncomputable section

namespace AutomorphicForm

namespace TwistedWeightedEuler

p2m_open

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

section Shape

variable (S : Finset (HeightOneSpectrum (𝓞 K))) (φ : Gad L → ℂ) (φa : Garch L → ℂ) (φf : Gfin L → ℂ)
  (φS : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ)

theorem φSp_of_mem {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ S) : φSp S φS v = φS v := by
  simp only [φSp, hv, if_true]

end Shape
end TwistedWeightedEuler
end AutomorphicForm
end
end P2MW.S_AutomorphicForm_exists_isTwistedWeightedOrbitalIntegralOn_baseChange_eq_mul_sum_prod_of_isSemiLocalFactorization
