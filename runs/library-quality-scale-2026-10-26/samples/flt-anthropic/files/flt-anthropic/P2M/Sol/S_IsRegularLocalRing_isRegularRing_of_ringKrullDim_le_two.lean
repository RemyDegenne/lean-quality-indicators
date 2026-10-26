import Mathlib
import Theorems.Thm_IsRegularLocalRing_isDomain
import Theorems.Thm_IsRegularLocalRing_uniqueFactorizationMonoid_of_ringKrullDim_le_two
import Theorems.Thm_IsIntegrallyClosed_isRegularLocalRing_localization_of_ne_maximalIdeal_of_ringKrullDim_le_two
import P2M.Util
namespace P2MW.S_IsRegularLocalRing_isRegularRing_of_ringKrullDim_le_two

set_option autoImplicit false

theorem solution
    (R : Type) [CommRing R] [IsRegularLocalRing R] (hdim : ringKrullDim R ≤ 2) :
    IsRegularRing R := by
  haveI : IsDomain R := IsRegularLocalRing.isDomain R
  haveI : UniqueFactorizationMonoid R := IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_two R hdim
  haveI : IsIntegrallyClosed R := inferInstance
  rw [isRegularRing_iff]
  intro p hp
  by_cases h : p = IsLocalRing.maximalIdeal R
  · subst h
    exact IsRegularLocalRing.of_ringEquiv
      (IsLocalization.atUnits R (IsLocalRing.maximalIdeal R).primeCompl (fun x ↦ by simp; exact fun a ↦ a)).toRingEquiv
  · exact IsIntegrallyClosed.isRegularLocalRing_localization_of_ne_maximalIdeal_of_ringKrullDim_le_two hdim p h
