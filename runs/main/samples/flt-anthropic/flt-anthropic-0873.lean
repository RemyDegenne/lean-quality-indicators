namespace P2MW.S_CohCarrier_heckeT_comm_of_prime

set_option autoImplicit false

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

open Matrix CongruenceSubgroup Matrix.SpecialLinearGroup

p2m_reactivate

namespace IharaSolComm

open scoped MatrixGroups

section DockHeckeT

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

theorem alpha_rep_distinct (q q' : Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper M H ℓ)))
    (hqq' : alpha ℓ * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q) *
      (alpha ℓ * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q'))⁻¹ ∈ (ιΓ M H).range) : q = q' := by
  obtain ⟨γ₀, hγ₀⟩ := hqq'
  have hg : ιΓ M H γ₀ * alpha ℓ = alpha ℓ * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q *
      (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q')⁻¹) := by
    rw [map_mul, map_inv, hγ₀, _root_.mul_inv_rev]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  have h01 := congrArg (fun u : GL (Fin 2) ℚ => (u : Matrix (Fin 2) (Fin 2) ℚ) 0 1) hg
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, alpha_coe, ιΓ_coe_apply] at h01
  simp at h01
  have hz : ((γ₀ : SL(2, ℤ)) 0 1) * (ℓ : ℤ) =
      (((CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q * (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q')⁻¹ :
        ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) 0 1) := by
    exact_mod_cast h01
  have hdvd : (ℓ : ℤ) ∣ (((CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q *
      (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q')⁻¹ : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) 0 1) :=
    Dvd.intro_left _ hz
  refine eq_of_rep_mul_inv_mem M H _ q q' ?_
  rw [Subgroup.mem_subgroupOf, CohCarrier.mem_Gamma0Upper]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).mpr hdvd

end DockHeckeT
end IharaSolComm
end P2MW.S_CohCarrier_heckeT_comm_of_prime
