set_option warningAsError true

@[expose] public section

open scoped Matrix

namespace LinearEquiv

universe u v

/-- The first projection of a supplied product equivalence, as a linear map
on the original rank-two free module. -/
def coefficientProductFirstMap (R : Type u) [Semiring R]
    (P : Type v) [AddCommMonoid P] [Module R P]
    (e : (Fin 2 → R) ≃ₗ[R] (R × P)) : (Fin 2 → R) →ₗ[R] R :=
  (LinearMap.fst R R P).comp e.toLinearMap

end LinearEquiv
end
