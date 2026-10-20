public section

namespace WeierstrassCurve

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

theorem localMinimalDiscriminant_ne_bot (W : WeierstrassCurve K) [W.IsElliptic] :
    W.localMinimalDiscriminant R ≠ ⊥ := by
  rw [localMinimalDiscriminant, ne_eq, Ideal.span_singleton_eq_bot]
  intro hΔ
  have hmap := congrArg (algebraMap R K) hΔ
  rw [integralModel_Δ_eq R (W.minimal R)] at hmap
  have hminimalΔ : (W.minimal R).Δ ≠ 0 := by
    obtain ⟨C, hC⟩ := W.exists_smul_eq_minimal R
    rw [← hC, variableChange_Δ]
    exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) W.isUnit_Δ.ne_zero
  exact hminimalΔ (by simpa using hmap)

end WeierstrassCurve
end
