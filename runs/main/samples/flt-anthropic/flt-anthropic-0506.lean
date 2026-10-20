namespace P2MW.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_diagonal_complex_eq_mul_integral_unitaryAverage

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

set_option linter.unusedSimpArgs false

open MeasureTheory TopologicalSpace Topology

open AutomorphicForm AutomorphicForm.GL2Twisted

noncomputable section

namespace P2mOIDiagC

scoped instance t2_GL : T2Space (GL (Fin 2) ℂ) := isEmbedding_glVal.t2Space

scoped instance sc_GL : SecondCountableTopology (GL (Fin 2) ℂ) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  exact isEmbedding_glVal.secondCountableTopology

scoped instance lc_GL : LocallyCompactSpace (GL (Fin 2) ℂ) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) ℂ) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → ℂ))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℂ))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

section Conj

theorem splitElt_conj (a₁ a₂ : ℂ) (ha : a₁ * a₂ ≠ 0) (γ : GL (Fin 2) ℂ)
    (hγ : (γ : Matrix (Fin 2) (Fin 2) ℂ) = !![a₁, 0; 0, a₂]) (b₁ b₂ : ℝ) (z : ℂ) (h : 0 < b₁ ∧ 0 < b₂)
    (k : GL (Fin 2) ℂ) :
    (twistedSplitElt (b₁ ^ 2) (b₂ ^ 2) (b₁ * z) ⟨pow_pos h.1 2, pow_pos h.2 2⟩ * k)⁻¹ * γ *
        (twistedSplitElt (b₁ ^ 2) (b₂ ^ 2) (b₁ * z) ⟨pow_pos h.1 2, pow_pos h.2 2⟩ * k) =
      k⁻¹ * U a₁ a₂ ha ((a₁ - a₂) * z) * k := by
  set S : GL (Fin 2) ℂ := twistedSplitElt (b₁ ^ 2) (b₂ ^ 2) (b₁ * z) ⟨pow_pos h.1 2, pow_pos h.2 2⟩ with hS
  have hSU : γ * S = S * U a₁ a₂ ha ((a₁ - a₂) * z) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hγ, hS, coe_splitElt b₁ b₂ z h, coe_U, Matrix.mul_fin_two, Matrix.mul_fin_two]
    simp only [EmbeddingLike.apply_eq_iff_eq, Matrix.vecCons_inj, and_true]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> ring
  have h1 : S⁻¹ * γ * S = U a₁ a₂ ha ((a₁ - a₂) * z) := by
    rw [mul_assoc, hSU, inv_mul_cancel_left]
  calc (S * k)⁻¹ * γ * (S * k) = k⁻¹ * (S⁻¹ * γ * S) * k := by simp only [mul_inv_rev, mul_assoc]
    _ = k⁻¹ * U a₁ a₂ ha ((a₁ - a₂) * z) * k := by rw [h1]

end Conj
end P2mOIDiagC
end
end P2MW.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_diagonal_complex_eq_mul_integral_unitaryAverage
