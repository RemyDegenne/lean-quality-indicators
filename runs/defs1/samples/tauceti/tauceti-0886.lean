public section

open CategoryTheory

open scoped TensorProduct

namespace TauCeti

namespace GeneralLinear

universe u v w

variable {R : Type u} [CommRing R]

variable {V : Type v} [AddCommMonoid V] [Module R V]

/-- The group of linear automorphisms of the scalar extension `A ⊗[R] V`. -/
abbrev scalarExtensionAutomorphisms (A : CommAlgCat.{w} R) :
    GrpCat.{max v w} :=
  GrpCat.of (LinearMap.GeneralLinearGroup A (A ⊗[R] V))

end GeneralLinear
end TauCeti
end
