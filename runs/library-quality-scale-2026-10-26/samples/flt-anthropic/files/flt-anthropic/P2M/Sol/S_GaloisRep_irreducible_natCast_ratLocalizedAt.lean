import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import P2M.Util
namespace P2MW.S_GaloisRep_irreducible_natCast_ratLocalizedAt

set_option autoImplicit false

theorem solution (q : ℕ) (hq : q.Prime) :
    Irreducible ((q : ℕ) : GaloisRep.ratLocalizedAt q) := by
  haveI : IsDiscreteValuationRing (GaloisRep.ratLocalizedAt q) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt q hq
  haveI hprime : (Ideal.span {(q : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)]
    exact Nat.prime_iff_prime_int.mp hq
  haveI := GaloisRep.isLocalization_ratLocalizedAt (p := q) hq
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]

  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {(q : ℤ)}) (GaloisRep.ratLocalizedAt q),
    Ideal.map_span, Set.image_singleton]
  all_goals first | rfl | simp
