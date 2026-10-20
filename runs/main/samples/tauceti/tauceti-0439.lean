public section

open PowerSeries

namespace TauCeti

theorem evalIntBivariateSeries_eq_tsum {K : Type*} [NormedCommRing K] [NormOneClass K]
    [CompleteSpace K] [IsUltrametricDist K]
    (u : K) (hu : ‖u‖ < 1) (v : K) (hv : ‖v‖ < 1) (f : ℤ⟦X⟧⟦X⟧) :
    evalIntBivariateSeries u hu v hv f =
      ∑' p : ℕ × ℕ, ((coeff p.1 (coeff p.2 f) : ℤ) : K) * u ^ p.1 * v ^ p.2 := by
  have hs := (summable_norm_intCast_mul_pow_mul_pow (K := K)
    (fun p ↦ coeff p.1 (coeff p.2 f)) hu hv).of_norm
  rw [evalIntBivariateSeries_apply]
  calc
    _ = ∑' b : ℕ, ∑' a : ℕ, ((coeff a (coeff b f) : ℤ) : K) * u ^ a * v ^ b := by
      apply tsum_congr
      intro b
      exact ((summable_intCast_mul_pow (fun a ↦ coeff a (coeff b f)) hu).tsum_mul_right
        (v ^ b)).symm
    _ = _ := hs.tsum_comm.trans hs.tsum_prod.symm

end TauCeti
end
