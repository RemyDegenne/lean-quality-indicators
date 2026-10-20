set_option maxRecDepth 2048

set_option backward.isDefEq.respectTransparency false

set_option warningAsError true

@[expose] public section

namespace RingedSpaces.Modules.BaseChange

open CategoryTheory CategoryTheory.Functor TopologicalSpace PullbackCoherence

universe u

variable {W X Y Z : AlgebraicGeometry.RingedSpace.{u, u}}

/-- Canonical normalization of the source of the identity-vertical square mate. -/
noncomputable def sourceIdentity (top : X ⟶ Z) :
    R top ⋙ L (𝟙 Z) ≅ R top :=
  isoWhiskerLeft (R top) (pullbackId Z) ≪≫ CategoryTheory.Functor.rightUnitor (R top)

end RingedSpaces.Modules.BaseChange
end
