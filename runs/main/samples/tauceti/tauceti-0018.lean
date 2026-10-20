public section

namespace TauCeti

open _root_.IsLocalRing Ideal MvPolynomial

section IsRegularRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

variable [IsRegularRing R] {π : R}

omit [IsRegularRing R] in
theorem isPrime_map_quotient_X_mul_X_sub_C_pow_iff (hπ : π ∈ maximalIdeal R) (n : ℕ) :
    (((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
      (NodeAlgebra.mk (π ^ n)).toRingHom).IsPrime ↔ n ≠ 0 := by
  refine ⟨?_, fun hn ↦ map_isPrime_of_surjective
    (f := (NodeAlgebra.mk (π ^ n)).toRingHom) (NodeAlgebra.mk_surjective _) ?_⟩
  · -- for `n = 0` the image of `x` is a unit
    rintro h rfl
    rw [pow_zero] at h
    have hX0 : X (0 : Fin 2) ∈
        (maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R) := by simp
    refine h.ne_top (eq_top_of_isUnit_mem _ (mem_map_of_mem _ hX0)
      (IsUnit.of_mul_eq_one (NodeAlgebra.coord (1 : R) 1) ?_))
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, NodeAlgebra.mk_X, map_one] using
      NodeAlgebra.coord_zero_mul_coord_one (1 : R)
  · rw [AlgHom.toRingHom_eq_coe, NodeAlgebra.ker_mk, span_le, Set.singleton_subset_iff,
      SetLike.mem_coe, mem_comap]
    simpa [hn] using hπ

end IsRegularRing
end TauCeti
end
