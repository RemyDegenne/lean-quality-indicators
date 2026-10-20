namespace P2MW.S_ModularCurve_meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two

set_option autoImplicit false

noncomputable section

open UpperHalfPlane ModularForm Complex SlashInvariantForm Derivative Filter ModularGroup

open scoped MatrixGroups Real Topology ModularForm Manifold Derivative Modular

namespace ModularCurve

namespace JMultiplicity

p2m_open

local notation "Δ" => ModularForm.discriminant

lemma case_generic {τ : ℍ} (h4 : E₄ τ ≠ 0) (h6 : E₆ τ ≠ 0) :
    analyticOrderAt (fun z : ℂ => jf (ofComplex z) - jf τ) (τ : ℂ) = (1 : ℕ) ∧
      Nat.card (MulAction.stabilizer SL(2, ℤ) τ) = 2 := by
  obtain ⟨c, hc0, hc⟩ := exists_D_jf_mul_Δ_eq
  have hD : D jf τ ≠ 0 := by
    intro h
    have := hc τ
    rw [h, zero_mul] at this
    exact mul_ne_zero hc0 (mul_ne_zero (pow_ne_zero _ h4) h6) this.symm
  have hd : deriv (jf ∘ ofComplex) (τ : ℂ) ≠ 0 := by
    rw [deriv_jf_eq _ τ.im_pos, ofComplex_apply]
    exact mul_ne_zero (by simp [Real.pi_ne_zero, Complex.I_ne_zero]) hD
  refine ⟨?_, ?_⟩
  · have h := (analyticAt_comp mdifferentiable_jf τ).analyticOrderAt_sub_eq_one_of_deriv_ne_zero hd
    rw [comp_apply_coe] at h
    exact h
  · rcases orbit_trichotomy τ with ⟨γ, rfl⟩ | ⟨γ, rfl⟩ | h
    · exact absurd ((E₆_smul_eq_zero_iff γ _).mpr E₆_I) h6
    · exact absurd ((E₄_smul_eq_zero_iff γ _).mpr E₄_ρ) h4
    · exact natCard_stabilizer_eq_two h

end JMultiplicity
end ModularCurve
end
end P2MW.S_ModularCurve_meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two
