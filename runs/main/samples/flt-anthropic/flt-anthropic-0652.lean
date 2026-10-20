namespace P2MW.S_ModularCurve_UVCrossingModel_sInf_dominantIndices_zero_mul_and_sSup_dominantIndices_mul

set_option maxHeartbeats 800000

set_option autoImplicit false

universe u

namespace EndSlopeSol

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

variable {W : Type u} [CommRing W]

theorem termOrder_natCast (v : W → ℕ∞) (E t : ℕ) (ab : PowerSeries W × PowerSeries W) (i : ℕ) :
    termOrder v E t ab (i : ℤ) = v (PowerSeries.coeff i ab.1) + ((i * t : ℕ) : ℕ∞) := by
  simp [termOrder, annulusWeight]

end EndSlopeSol
end P2MW.S_ModularCurve_UVCrossingModel_sInf_dominantIndices_zero_mul_and_sSup_dominantIndices_mul
