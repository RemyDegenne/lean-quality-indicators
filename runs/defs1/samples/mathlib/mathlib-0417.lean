@[expose] public section

universe u v w

variable {S T : Type*}

variable {R : Type*} {M N P A : Type*}

open LinearMap (BilinMap BilinForm)

section

variable {n : Type w} [Fintype n] [DecidableEq n]

variable [CommRing R] [AddCommMonoid M] [Module R M]

variable [Invertible (2 : R)]

namespace QuadraticForm

section Discriminant

section Basis

open Module

variable [AddCommGroup N] [Module R N] (b : Basis n R N) (Q : QuadraticForm R N)

/-- The discriminant of a quadratic form `Q : QuadraticForm R N` generalizes the discriminant
  of a quadratic polynomial. -/
noncomputable def discr : R := (Q.toMatrix b).det

end Basis
end Discriminant
end QuadraticForm
end
end
