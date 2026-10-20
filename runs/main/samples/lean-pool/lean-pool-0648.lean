@[expose] public section

namespace Bananas

open Utilities

theorem int_eq_of_emod_sub_eq_zero_of_fundamental
    {k b c : ℤ} (hk : 0 < k)
    (hb0 : 0 ≤ b) (hb : b < k)
    (hc0 : 0 ≤ c) (hc : c < k)
    (hmod : (b - c) % k = 0) :
    b = c := by
  have hDvd : k ∣ b - c := (Int.dvd_iff_emod_eq_zero).mpr hmod
  by_contra hne
  have hAbsPos : 0 < (b - c).natAbs :=
    Int.natAbs_pos.mpr (sub_ne_zero.mpr hne)
  have hAbsLt : (b - c).natAbs < k.natAbs := by
    have hCast : ((b - c).natAbs : ℤ) < (k.natAbs : ℤ) := by
      rw [Int.natCast_natAbs, Int.natCast_natAbs, abs_of_pos hk, abs_lt]
      omega
    exact_mod_cast hCast
  have hzero : b - c = 0 :=
    Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hDvd hAbsLt
  exact hne (sub_eq_zero.mp hzero)

end Bananas
end
