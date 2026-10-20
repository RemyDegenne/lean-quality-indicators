namespace P2MW.S_ModularCurve_UVCrossingModel_exists_pow_eq_unit_mul_U_of_isCyclic_of_isUnramifiedAt_of_residue_thicknessOne

set_option autoImplicit false

open ModularCurve ModularCurve.UVCrossingModel

namespace KummerClass44

section K3b

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R K] in
theorem UnitAt.mul {P : Ideal R} [P.IsPrime] {x y : K} (hx : UnitAt K P x) (hy : UnitAt K P y) :
    UnitAt K P (x * y) := by
  obtain ⟨r, s, hr, hs, h⟩ := hx
  obtain ⟨r', s', hr', hs', h'⟩ := hy
  refine ⟨r * r', s * s', fun hh => (Ideal.IsPrime.mem_or_mem inferInstance hh).elim hr hr',
    fun hh => (Ideal.IsPrime.mem_or_mem inferInstance hh).elim hs hs', ?_⟩
  rw [map_mul, map_mul]
  linear_combination (y * algebraMap R K s') * h + algebraMap R K r * h'

end K3b
end KummerClass44
end P2MW.S_ModularCurve_UVCrossingModel_exists_pow_eq_unit_mul_U_of_isCyclic_of_isUnramifiedAt_of_residue_thicknessOne
