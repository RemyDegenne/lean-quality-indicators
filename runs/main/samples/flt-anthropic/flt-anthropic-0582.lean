namespace P2MW.S_ModularCurve_FullLevel_Diamond_ker_mem_minimalPrimes_of_levelModuliPackageAbs_qExpansion_of_dense_of_exists_ringHom_rigidDataH1Pow

set_option autoImplicit false

p2m_open

open scoped MatrixGroups

namespace ModularCurve

namespace KerMin

p2m_open

theorem transcendental_coeffEmb_jq (L : Type) [Field L] [CharZero L] :
    Transcendental L (ModularCurve.coeffEmb L ModularCurve.jq) := by
  rw [transcendental_iff]
  intro p hp
  by_contra hp0
  set n := p.natDegree with hn
  have hlead : p.coeff n ≠ 0 := by
    rw [hn]; exact mt Polynomial.leadingCoeff_eq_zero.mp hp0
  apply hlead
  have hc := congrArg (fun y : LaurentSeries L => y.coeff (-(n : ℤ))) hp
  simp only [HahnSeries.coeff_zero] at hc
  rw [Polynomial.aeval_eq_sum_range, ← hn, HahnSeries.coeff_sum, Finset.sum_range_succ,
    Finset.sum_eq_zero, zero_add] at hc
  · rw [Algebra.smul_def, ModularCurve.algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul, ← map_pow,
      ModularCurve.coeffEmb_coeff, ModularCurve.coeff_jq_pow_self, map_one, mul_one] at hc
    exact hc
  · intro i hi
    rw [Finset.mem_range] at hi
    rw [Algebra.smul_def, ModularCurve.algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul, ← map_pow,
      ModularCurve.coeffEmb_coeff, ModularCurve.coeff_jq_pow_of_lt (by omega), map_zero, mul_zero]

end KerMin
end ModularCurve
end P2MW.S_ModularCurve_FullLevel_Diamond_ker_mem_minimalPrimes_of_levelModuliPackageAbs_qExpansion_of_dense_of_exists_ringHom_rigidDataH1Pow
