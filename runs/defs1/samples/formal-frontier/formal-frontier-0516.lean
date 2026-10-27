public section

set_option warningAsError true

set_option backward.isDefEq.respectTransparency.types false

set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

universe v

namespace SheafCohomology.ConePullbackSections

variable {X Y : TopCat.{v}} (f : X ⟶ Y)

variable {F : Y.Sheaf (Type v)} {G : X.Sheaf (Type v)}

/-- After adjunction, a section may be restricted to any smaller inverse-image open. -/
def restrictedAdjointSectionMap
    (a : (TopCat.Sheaf.pullback (Type v) f).obj F ⟶ G)
    (U : Opens Y) (V : Opens X) (hV : V ≤ (Opens.map f).obj U) :
    F.1.obj (op U) ⟶ G.1.obj (op V) :=
  adjointSectionMap f a U ≫ G.1.map (homOfLE hV).op

end SheafCohomology.ConePullbackSections
end
end
