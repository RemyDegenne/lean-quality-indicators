public section

set_option warningAsError true

set_option linter.style.haveILetI false

set_option backward.defeqAttrib.useBackward true

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v

noncomputable section

namespace AlgebraicGeometry.SheafedSpace

variable {J : Type v} [SmallCategory J]
    (S : Jᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} CommRingCat.{v}) (m : Cone S)

theorem colimit_ι_nativeCommRingGlobalSectionsComparison (i : J) :
    colimit.ι (S.rightOp ⋙ SheafedSpace.Γ) i ≫
        nativeCommRingGlobalSectionsComparison S m =
      SheafedSpace.Γ.map (m.π.app (op i)).op := by
  simpa only [nativeCommRingGlobalSectionsComparison,
    nativeCommRingGlobalSectionsCocone] using
    (colimit.ι_desc (nativeCommRingGlobalSectionsCocone S m) i)

end AlgebraicGeometry.SheafedSpace
end
end
