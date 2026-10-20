public section

open scoped nonZeroDivisors Polynomial

variable {R : Type*} [CommRing R]

namespace Polynomial

section FractionMap

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

section IsIntegrallyClosed

open IsIntegrallyClosed

theorem Monic.irreducible_iff_irreducible_map_fraction_map [IsIntegrallyClosed R] {p : R[X]}
    (h : p.Monic) : Irreducible p ↔ Irreducible (p.map <| algebraMap R K) := by
  /- The ← direction follows from `IsPrimitive.irreducible_of_irreducible_map_of_injective`.
       For the → direction, it is enough to show that if `(p.map <| algebraMap R K) = a * b` and
       `a` is not a unit then `b` is a unit -/
  refine
    ⟨fun hp =>
      irreducible_iff.mpr
        ⟨hp.not_isUnit.imp h.isPrimitive.isUnit_iff_isUnit_map.mpr, fun a b H =>
          or_iff_not_imp_left.mpr fun hₐ => ?_⟩,
      fun hp =>
      h.isPrimitive.irreducible_of_irreducible_map_of_injective (IsFractionRing.injective R K) hp⟩
  obtain ⟨a', ha⟩ := eq_map_mul_C_of_dvd K h (dvd_of_mul_right_eq b H.symm)
  obtain ⟨b', hb⟩ := eq_map_mul_C_of_dvd K h (dvd_of_mul_left_eq a H.symm)
  have : a.leadingCoeff * b.leadingCoeff = 1 := by
    rw [← leadingCoeff_mul, ← H, Monic.leadingCoeff (h.map <| algebraMap R K)]
  rw [← ha, ← hb, mul_comm _ (C b.leadingCoeff), mul_assoc, ← mul_assoc (C a.leadingCoeff), ←
    C_mul, this, C_1, one_mul, ← Polynomial.map_mul] at H
  rw [← hb, ← Polynomial.coe_mapRingHom]
  refine
    IsUnit.mul (IsUnit.map _ (Or.resolve_left (hp.isUnit_or_isUnit ?_) (show ¬IsUnit a' from ?_)))
      (isUnit_iff_exists_inv'.mpr
        (Exists.intro (C a.leadingCoeff) <| by rw [← C_mul, this, C_1]))
  · exact Polynomial.map_injective _ (IsFractionRing.injective R K) H
  · by_contra h_contra
    refine hₐ ?_
    rw [← ha, ← Polynomial.coe_mapRingHom]
    exact
      IsUnit.mul (IsUnit.map _ h_contra)
        (isUnit_iff_exists_inv.mpr
          (Exists.intro (C b.leadingCoeff) <| by rw [← C_mul, this, C_1]))

end IsIntegrallyClosed
end FractionMap
end Polynomial
end
