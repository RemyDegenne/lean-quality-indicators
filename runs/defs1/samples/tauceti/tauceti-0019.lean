public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup TauCeti ComplexConjugate

open scoped MatrixGroups

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

namespace Newform

/-- **A new eigenvector, normalised, is a newform.** A nonzero cusp form of nebentypus `χ` in the
new subspace that is an eigenvector of the Hecke ring at every prime not dividing `N`, divided
by its first coefficient (which is nonzero). -/
noncomputable def ofForallPrime {F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hχ : F ∈ cuspFormCharSpace k χ) (hnew : F ∈ cuspFormsNew N k) (hF : F ≠ 0)
    (h : ∀ p : ℕ, p.Prime → Nat.Coprime p N → ∃ c : ℂ,
      heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p) ⟨F, hχ⟩ = c • ⟨F, hχ⟩) :
    Newform N k where
  toEigenformAwayFromLevel :=
    EigenformAwayFromLevel.ofForallPrime (f := ((qExpansion 1 F).coeff 1)⁻¹ • F)
      (Submodule.smul_mem _ _ hχ)
      (smul_ne_zero
        (inv_ne_zero (qExpansion_coeff_one_ne_zero_of_mem_cuspFormsNew hχ hnew hF h)) hF)
      fun p hp hpN ↦ by
        obtain ⟨c, hc⟩ := h p hp hpN
        -- the rescaled form, as an element of `S_k(N, χ)`, is the rescaled element
        have hmk : (⟨((qExpansion 1 F).coeff 1)⁻¹ • F, Submodule.smul_mem _ _ hχ⟩ :
            cuspFormCharSpace k χ) = ((qExpansion 1 F).coeff 1)⁻¹ • ⟨F, hχ⟩ :=
          Subtype.ext (Submodule.coe_smul _ (⟨F, hχ⟩ : cuspFormCharSpace k χ)).symm
        exact ⟨c, by rw [hmk, map_smul, hc, smul_comm]⟩
  isNew := by
    rw [EigenformAwayFromLevel.ofForallPrime_toCuspForm]
    exact Submodule.smul_mem _ _ hnew
  isNorm := by
    rw [EigenformAwayFromLevel.ofForallPrime_toCuspForm,
      ← CuspForm.qExpansionCoeffₗ_apply one_pos (one_mem_strictPeriods_Gamma1_map N), map_smul,
      CuspForm.qExpansionCoeffₗ_apply, smul_eq_mul,
      inv_mul_cancel₀ (qExpansion_coeff_one_ne_zero_of_mem_cuspFormsNew hχ hnew hF h)]

end Newform
end HeckeRing.GL2
end
