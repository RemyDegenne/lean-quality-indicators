public section

set_option autoImplicit true

set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson.Proofs

open Subgroup CFSG.FeitThompson

open CFSG.FeitThompson.Prep05

universe u

open scoped Classical in
theorem FPF_type_iii_iv_two_coherent_layers
    (h₁ : Statements.FPF_type_iii_iv_core_elementary_chief_kernel_trivial.{u})
    (h₂ : Statements.FPF_type_iii_iv_second_derived_fitting.{u})
    (h₃ : Statements.FPF_type_iii_v_extended_dade_support.{u})
    (h₄ : Statements.FPF_type_iii_v_induced_family_noncoherence.{u})
    (h₅ : Statements.FPF_type_iii_v_second_factor_prime.{u}) :
    Statements.FPF_type_iii_iv_two_coherent_layers.{u} := by
  classical
  intro G _ _ hG M U W₁ W₂ hM htype hc C hC S₁ S₂ hS₁ hS₂
  obtain ⟨hdisj, hunion, hcoh₂⟩ :=
    twoCoherentLayers_residual h₁ h₂ h₃ h₄ h₅ G hG M U W₁ W₂ hM htype hc C hC S₁ S₂ hS₁ hS₂
  subst hC
  refine ⟨sup_hallCoreIn_centralizer_eq_commutator_commutator h₂ hG hM htype hc,
    centralizer_eq_commutator_self h₁ hG hM htype hc,
    le_normalizer_centralizer h₅ hG hM htype hc, hdisj, ?_, ?_, hunion, ?_, hcoh₂, ?_, ?_, ?_, ?_⟩
  · rw [hS₁]; exact fun f hf => star_mem_indFamKer hf
  · rw [hS₂]; exact fun f hf => star_mem_indFamDetectKer hf
  · rw [hS₁]; exact hasCoherentMap_layer_one h₂ h₃ h₄ hG hM htype hc
  · rw [hunion]
    exact not_hasCoherentMap_indFamKer_centralizer h₁ h₃ h₄ h₅ hG hM htype hc
  · rw [hS₁]; exact (layer_one_subset_Irr h₂ hG hM htype hc).1
  · rw [hS₁]; exact (layer_one_subset_Irr h₂ hG hM htype hc).2
  · rw [hS₁]; exact exists_card_layer_one h₂ h₅ hG hM htype hc

end CFSG.FeitThompson.Proofs
end
