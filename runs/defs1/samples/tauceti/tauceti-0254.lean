public section

open CategoryTheory

namespace TauCeti

universe u v w

open GradedLinearQuiver

namespace AInfinityCategory

variable {R : Type w} [CommRing R] {C : Type u} [GradedLinearQuiver.{u, v, w} R C]
  (𝒞 : AInfinityCategory R C)

/-- The closed degree-zero morphisms from `X` to `Y`. -/
noncomputable def homCyclesZero (X Y : C) : Submodule R (homModule (R := R) X Y) :=
  (grading (R := R) X Y).piece 0 ⊓ LinearMap.ker (𝒞.homDifferential X Y)

end AInfinityCategory
end TauCeti
end
