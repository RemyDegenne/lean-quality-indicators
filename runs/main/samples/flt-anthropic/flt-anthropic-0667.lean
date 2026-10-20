namespace P2MW.S_AutomorphicForm_isOrbitalIntegral_indicator_scalar_localIntegralSet_and_principalCongruence_of_depth_of_forall_not_diagonal

set_option autoImplicit false

open MeasureTheory NumberField

open IsDedekindDomain

open scoped TensorProduct

open scoped TensorProduct.RightActions

open scoped Matrix

noncomputable section

namespace EllGermBridge

open AutomorphicForm

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

scoped instance secondCountable_localGL : SecondCountableTopology (GL (Fin 2) (v.adicCompletion K)) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → v.adicCompletion K))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (v.adicCompletion K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

section Integrality

theorem v_det_eq_sq_of_v_lt (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
    (hYint : Valued.v Y.det ≤ 1 ∧ Valued.v Y.trace ≤ 1) (α β : v.adicCompletion K)
    (hβα : Valued.v β < Valued.v α) :
    Valued.v (α • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) + β • Y).det = Valued.v α ^ 2 := by
  have hα0 : α ≠ 0 := by rintro rfl; rw [map_zero] at hβα; exact not_lt_zero hβα
  have hvα0 : Valued.v α ≠ 0 := (Valuation.ne_zero_iff _).2 hα0
  have hc : Valued.v (β / α) < 1 := by
    rw [map_div₀]; exact (div_lt_one₀ (zero_lt_iff.2 hvα0)).2 hβα
  have hX : (α • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) + β • Y).det =
      α ^ 2 * (1 + ((β / α) * Y.trace + (β / α) ^ 2 * Y.det)) := by
    rw [det_smul_one_add_smul]; field_simp; ring
  have hsmall : Valued.v ((β / α) * Y.trace + (β / α) ^ 2 * Y.det) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]; exact mul_lt_one_of_lt_of_le hc hYint.2
    · rw [map_mul, map_pow, pow_two]; exact mul_lt_one_of_lt_of_le (mul_lt_one_of_lt_of_le hc hc.le) hYint.1
  rw [hX, map_mul, map_pow, Valuation.map_one_add_of_lt _ hsmall, mul_one]

end Integrality
end EllGermBridge
end
end P2MW.S_AutomorphicForm_isOrbitalIntegral_indicator_scalar_localIntegralSet_and_principalCongruence_of_depth_of_forall_not_diagonal
