import Mathlib
import P2M.Util
namespace P2MW.S_IsLocalRing_isUnit_natCast_guardPrime_sub_one_div_two_of_charP_two

set_option autoImplicit false

theorem solution
    (R : Type*) [CommRing R] [IsLocalRing R] [CharP (IsLocalRing.ResidueField R) 2]
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) :
    IsUnit (((ℓg - 1) / 2 : ℕ) : R) := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_natCast]
  intro h
  have hd := (CharP.cast_eq_zero_iff (IsLocalRing.ResidueField R) 2 _).mp h
  omega
