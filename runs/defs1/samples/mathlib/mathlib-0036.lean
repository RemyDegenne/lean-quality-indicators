@[expose] public section

universe u v w

variable {S T : Type*}

variable {R : Type*} {M N P A : Type*}

open LinearMap (BilinMap BilinForm)

namespace QuadraticMap

section Comp

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

variable [AddCommMonoid P] [Module R P]

/-- Compose a quadratic map with a linear function on the left. -/
@[simps! +simpRhs]
def _root_.LinearMap.compQuadraticMap' [CommSemiring S] [Algebra S R] [Module S N] [Module S M]
    [IsScalarTower S R N] [IsScalarTower S R M] [Module S P]
    (f : N →ₗ[S] P) (Q : QuadraticMap R M N) : QuadraticMap S M P :=
  _root_.LinearMap.compQuadraticMap f Q.restrictScalars

end Comp
end QuadraticMap
end
