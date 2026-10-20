namespace P2MW.S_ModularCurve_UVCrossingModel_exists_pow_eq_unit_mul_U_of_isCyclic_of_isUnramifiedAt_of_residue_of_isPrimitiveRoot_mul

set_option autoImplicit false

open ModularCurve ModularCurve.UVCrossingModel

namespace KummerClass44

section K2

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]

theorem exists_mul_eq_mul_pow_of_irreducible (q : Ideal A) [q.IsPrime]
    [IsDiscreteValuationRing (Localization.AtPrime q)]
    (π₀ : A) (hirr : Irreducible (algebraMap A (Localization.AtPrime q) π₀))
    (r : A) (hr : r ≠ 0) :
    ∃ (a : ℕ) (r' s' : A), r' ∉ q ∧ s' ∉ q ∧ r * s' = r' * π₀ ^ a := by
  have hinj : Function.Injective (algebraMap A (Localization.AtPrime q)) :=
    IsLocalization.injective _ q.primeCompl_le_nonZeroDivisors
  have hr' : algebraMap A (Localization.AtPrime q) r ≠ 0 := (map_ne_zero_iff _ hinj).mpr hr
  obtain ⟨a, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr' hirr
  obtain ⟨⟨r', s'⟩, hrs⟩ := IsLocalization.mk'_surjective q.primeCompl (u : Localization.AtPrime q)
  dsimp only at hrs
  have hr'q : r' ∉ q := by
    have : IsUnit (IsLocalization.mk' (Localization.AtPrime q) r' s') := by rw [hrs]; exact u.isUnit
    exact (IsLocalization.AtPrime.isUnit_mk'_iff (Localization.AtPrime q) q r' s').mp this
  refine ⟨a, r', s', hr'q, s'.2, hinj ?_⟩
  rw [map_mul, map_mul, map_pow, hu, ← hrs]
  rw [← IsLocalization.mk'_spec (Localization.AtPrime q) r' s']
  ring

end K2
end KummerClass44
end P2MW.S_ModularCurve_UVCrossingModel_exists_pow_eq_unit_mul_U_of_isCyclic_of_isUnramifiedAt_of_residue_of_isPrimitiveRoot_mul
