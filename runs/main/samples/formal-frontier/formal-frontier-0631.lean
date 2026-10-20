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

theorem restrictedAdjointSectionMap_restrict_target
    (a : (TopCat.Sheaf.pullback (Type v) f).obj F ⟶ G)
    (U : Opens Y) {V V' : Opens X}
    (hV : V ≤ (Opens.map f).obj U) (hV' : V' ≤ V) :
    restrictedAdjointSectionMap f a U V' (hV'.trans hV) =
      restrictedAdjointSectionMap f a U V hV ≫ G.1.map (homOfLE hV').op := by
  unfold restrictedAdjointSectionMap
  rw [show (homOfLE (hV'.trans hV)).op =
    (homOfLE hV).op ≫ (homOfLE hV').op from Subsingleton.elim _ _]
  rw [G.1.map_comp, Category.assoc]

end SheafCohomology.ConePullbackSections
end
end
