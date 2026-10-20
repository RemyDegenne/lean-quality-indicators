public section

namespace WeierstrassCurve

open IsLocalRing IsDiscreteValuationRing TauCeti

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

variable [PerfectField (ResidueField R)]

variable {R}

@[simp]
theorem forall_reductionSymbol_ne_I_iff (W : WeierstrassCurve K) [W.IsElliptic] :
    (∀ n, W.reductionSymbol R ≠ .I n) ↔ (W.minimal R).HasAdditiveReduction R := by
  obtain ⟨W', D, ϖ, hmin, hD, hϖ, h⟩ := W.exists_isTateTerminal_reductionSymbol R
  obtain ⟨C₀, hC₀⟩ := W.exists_smul_eq_minimal R
  have : (W.minimal R).IsElliptic := hC₀ ▸ inferInstance
  rw [← h.hasAdditiveReduction_iff (K := K) hϖ,
    hasAdditiveReduction_iff_of_isMinimal_smul R (W₁ := W.minimal R) (W₂ := W'.baseChange K)
      (D * C₀⁻¹) (by rw [mul_smul, ← hC₀, inv_smul_smul, hD])]

end WeierstrassCurve
end
