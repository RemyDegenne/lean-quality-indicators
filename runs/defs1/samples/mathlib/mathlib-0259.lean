@[expose] public section

noncomputable section

universe v u

open TopologicalSpace CategoryTheory Opposite Topology

open CategoryTheory.Limits AlgebraicGeometry.PresheafedSpace

open CategoryTheory.GlueData

namespace AlgebraicGeometry

namespace Scheme

attribute [instance] GlueData.f_open

section IsLocallyDirected

open TopologicalSpace.Opens

universe w

variable {J : Type w} [Category.{v} J] (F : J ⥤ Scheme.{u})

variable [∀ {i j} (f : i ⟶ j), IsOpenImmersion (F.map f)]

namespace IsLocallyDirected

variable [(F ⋙ forget).IsLocallyDirected]

variable [Quiver.IsThin J]

variable [Small.{u} J]

local notation3:max "↓"j:arg => Equiv.symm (equivShrink _) j

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The open cover of the colimit of a locally directed diagram by the components. -/
@[simps! I₀ X f]
def openCover : (colimit F).OpenCover :=
  Cover.copy ((coverOfIsIso ((isColimit F).coconePointUniqueUpToIso (colimit.isColimit F)).hom).bind
    fun i ↦ (glueData F).openCover) J F.obj (colimit.ι F)
    ((equivShrink J).trans (Equiv.uniqueSigma fun (_ : Unit) ↦ Shrink J).symm)
    (fun _ ↦ F.mapIso (eqToIso (by simp [GlueData.openCover, glueData]))) fun i ↦ by
  change colimit.ι F i = _ ≫ (glueData F).ι (equivShrink J i) ≫ _
  simp [← Category.assoc, ← Iso.comp_inv_eq, cocone]

end IsLocallyDirected
end IsLocallyDirected
end Scheme
end AlgebraicGeometry
end
end
