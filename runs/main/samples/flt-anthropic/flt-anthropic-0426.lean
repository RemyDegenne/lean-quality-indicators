namespace P2MW.S_TwistedUnipotentTerm_isLocallyConstant_integral_setIntegral_integral_semiLocalCharacter_mul_twist_and_hasCompactSupport

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

open scoped TensorProduct Pointwise

attribute [local instance] AutomorphicForm.glBorelOf

noncomputable section

namespace K6A

section Main

open scoped TensorProduct.RightActions

open Topology Filter

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)

theorem continuous_sG [IsTopologicalRing (L ⊗[K] v.adicCompletion K)] : Continuous (sG K L v σ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun κ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
      (κ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).map
        (Algebra.TensorProduct.congr σ (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K))
    exact Units.continuous_val.matrix_map (continuous_congr K L v σ)
  · show Continuous fun κ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
      (((sG K L v σ κ)⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))
    have : (fun κ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
        (((sG K L v σ κ)⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
          Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) =
        fun κ => ((κ⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) _).map
          (Algebra.TensorProduct.congr σ (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)) := by
      funext κ; rw [← map_inv]; rfl
    rw [this]
    exact Units.continuous_coe_inv.matrix_map (continuous_congr K L v σ)

end Main
end K6A
end
end P2MW.S_TwistedUnipotentTerm_isLocallyConstant_integral_setIntegral_integral_semiLocalCharacter_mul_twist_and_hasCompactSupport
