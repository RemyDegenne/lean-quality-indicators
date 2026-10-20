namespace P2MW.S_AutomorphicForm_integrableOn_and_measurable_and_constantTerm_setIntegral_mul_finsum_borel_div_mem_eq_setIntegral_mul_integral_finsum_inv_unipotentGL2_mul

attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions

set_option autoImplicit false

noncomputable section

namespace R4FoldCT

set_option maxHeartbeats 1600000

open MeasureTheory MeasureTheory.Measure NumberField Filter Function Set AutomorphicForm

open scoped ENNReal NNReal Topology Pointwise

section Fold

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
  (A : Set L) (φ : AdelicGL2 (𝓞 L) L → ℂ) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)

def princEquiv : Lˣ ≃ (princ L).range := (MonoidHom.ofInjective (princ_injective L)).toEquiv

end Fold
end R4FoldCT
end
end P2MW.S_AutomorphicForm_integrableOn_and_measurable_and_constantTerm_setIntegral_mul_finsum_borel_div_mem_eq_setIntegral_mul_integral_finsum_inv_unipotentGL2_mul
