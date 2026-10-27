@[expose] public section

open TopologicalSpace CategoryTheory Opposite Topology

open CategoryTheory.Limits

namespace AlgebraicGeometry

universe w v v₁ v₂ u

variable {C : Type u} [Category.{v} C]

/-- A morphism of SheafedSpaces is an open immersion if it is an open immersion as a morphism
of PresheafedSpaces
-/
abbrev SheafedSpace.IsOpenImmersion {X Y : SheafedSpace C} (f : X ⟶ Y) : Prop :=
  PresheafedSpace.IsOpenImmersion f.hom

end AlgebraicGeometry
end
