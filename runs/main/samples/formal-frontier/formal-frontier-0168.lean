public section

set_option warningAsError true

set_option linter.style.haveILetI false

set_option backward.defeqAttrib.useBackward true

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe v

noncomputable section

namespace AlgebraicGeometry.SheafedSpace.NativeCylinderLimit

variable {ι : Type v} [Preorder ι] [IsDirectedOrder ι]

variable {C : Type (v + 1)} [Category.{v} C]

variable (N : ιᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} C) (i0 : ι)

theorem restrictedLift_fac (m : Cone N) (hm : IsLimit m)
    (U0 : Opens (N.obj (op i0))) (t : Cone (restricted N i0 U0)) :
    restrictedLift N i0 m hm U0 t ≫
      m.pt.ofRestrict (coneOpen N i0 m U0).isOpenEmbedding =
      originalLift N i0 m hm U0 t := by
  apply InducedCategory.hom_ext
  unfold restrictedLift
  dsimp
  exact PresheafedSpace.IsOpenImmersion.lift_fac _ _
    (originalLift_range N i0 m hm U0 t)

end AlgebraicGeometry.SheafedSpace.NativeCylinderLimit
end
end
