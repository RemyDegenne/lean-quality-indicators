@[expose] public section

open Metric Set Filter Complex

open scoped Topology Real

namespace TauCeti

namespace DavisKahan

universe u

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

section One

variable (A : H →L[ℂ] H) {center radius : ℝ}

omit [CompleteSpace H] in
theorem ringInverse_smul_one_sub_eq_principal_add_remainder
    {z : ℂ} (hz : z ∉ spectrum ℂ A) (hzc : z ≠ (center : ℂ)) :
    Ring.inverse (z • (1 : H →L[ℂ] H) - A) =
      (z - (center : ℂ))⁻¹ • (1 : H →L[ℂ] H) +
        (z - (center : ℂ))⁻¹ •
          ((A - (center : ℂ) • (1 : H →L[ℂ] H)) *
            Ring.inverse (z • (1 : H →L[ℂ] H) - A)) := by
  have hne : z - (center : ℂ) ≠ 0 := sub_ne_zero.mpr hzc
  set R := Ring.inverse (z • (1 : H →L[ℂ] H) - A) with hR
  have hcancel : (z • (1 : H →L[ℂ] H) - A) * R = 1 :=
    Ring.mul_inverse_cancel _ (isUnit_smul_one_sub_of_notMem_spectrum hz)
  -- `(z - c) • R = 1 + (A - c) * R`, then divide by `z - c`.
  have hkey : (z - (center : ℂ)) • R =
      1 + (A - (center : ℂ) • (1 : H →L[ℂ] H)) * R := by
    have hsplit : z • (1 : H →L[ℂ] H) - A =
        (z - (center : ℂ)) • (1 : H →L[ℂ] H) -
          (A - (center : ℂ) • (1 : H →L[ℂ] H)) := by
      rw [sub_smul]; abel
    rw [hsplit, sub_mul, smul_mul_assoc, one_mul] at hcancel
    exact sub_eq_iff_eq_add.mp hcancel
  rw [← smul_add, ← hkey, smul_smul, inv_mul_cancel₀ hne, one_smul]

end One
end DavisKahan
end TauCeti
end
