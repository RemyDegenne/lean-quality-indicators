@[expose] public section

universe u

open CategoryTheory

open TopCat

open TopologicalSpace Topology

open Opposite

open CategoryTheory.Category CategoryTheory.Functor

namespace AlgebraicGeometry

attribute [instance] LocallyRingedSpace.isLocalRing

namespace LocallyRingedSpace

variable (X : LocallyRingedSpace.{u})

theorem Γ_def : Γ = forgetToSheafedSpace.op ⋙ SheafedSpace.Γ :=
  rfl

end LocallyRingedSpace
end AlgebraicGeometry
end
