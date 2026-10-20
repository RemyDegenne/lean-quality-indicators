public section

open QuadraticMap

open scoped Matrix

universe u v w

namespace QuadraticMap

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

variable (Q : QuadraticForm K V) [NeZero (2 : K)]

open TauCeti.QuadraticMap (isUnit_sub_or_add_of_map_eq orthogonalGroupEquivIsometryEquiv
  reflectionOrthogonal reflection_add_apply_eq_neg_of_map_eq reflection_sub_apply_eq_of_map_eq
  reflection)

@[simp↓]
theorem reflectionTransport_apply (x y : V) (hxy : Q x = Q y) (hy : Q y ≠ 0) :
    (Q.reflectionTransport x y hxy hy : V ≃ₗ[K] V) x = y := by
  by_cases hsub : Q (x - y) ≠ 0
  · let := (isUnit_iff_ne_zero.mpr hsub).invertible
    simpa using reflection_sub_apply_eq_of_map_eq Q x y hxy
  · have hadd := (isUnit_sub_or_add_of_map_eq Q x y hxy hy).resolve_left
      (by simpa only [isUnit_iff_ne_zero] using hsub)
    let := hadd.invertible
    let := (isUnit_iff_ne_zero.mpr hy).invertible
    have hneg := reflection_add_apply_eq_neg_of_map_eq Q x y hxy
    simp [reflectionTransport_eq_reflection_mul_reflection Q x y hxy hy
      (not_ne_iff.mp hsub), hneg, map_neg]

end QuadraticMap
end
