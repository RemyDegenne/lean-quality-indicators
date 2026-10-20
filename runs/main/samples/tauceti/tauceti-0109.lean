public section

namespace WeierstrassCurve

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open scoped nonZeroDivisors

variable (O : Type*) [CommRing O] [IsDedekindDomain O]
  {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]

@[simp]
theorem count_weierstrassDefectIdeal_eq_obstructionExponentAt
    (W : WeierstrassCurve K) (v : HeightOneSpectrum O) [W.IsElliptic] [IsIntegral O W] :
    ((Associates.mk v.asIdeal).count
      (Associates.mk (weierstrassDefectIdeal O W)).factors : ℤ) =
      obstructionExponentAt O v W := by
  rw [weierstrassDefectIdeal_def,
    Ideal.count_finprod_asIdeal_pow (hasFiniteMulSupport_pow_obstructionExponentAt_toNat O W) v]
  have : IsIntegral (Localization.AtPrime v.asIdeal) W :=
    IsIntegral.of_isScalarTower (R := O) W
  exact Int.toNat_of_nonneg (obstructionExponentAt_nonneg_of_isIntegral O v W)

end WeierstrassCurve
end
