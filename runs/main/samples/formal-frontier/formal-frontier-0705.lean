public section

set_option warningAsError true

set_option linter.style.haveILetI false

set_option backward.defeqAttrib.useBackward true

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v

noncomputable section

namespace AlgebraicGeometry.SheafedSpace.NativeCylinderLimit

variable {ι : Type v} [Preorder ι] [IsDirectedOrder ι]

variable {C : Type (v + 1)} [Category.{v} C]

variable (S : ιᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} C)
  (i0 j : ι) (h : i0 ≤ j) (U : Opens (S.obj (op i0)))

theorem namedRestrictCast_fac (X : SheafedSpace.{v + 1, v, v} C)
    {V W : Opens X} (e : V = W) :
    eqToHom (congrArg (fun A : Opens X => X.restrict A.isOpenEmbedding) e) ≫
      X.ofRestrict W.isOpenEmbedding = X.ofRestrict V.isOpenEmbedding := by
  cases e
  simp

end AlgebraicGeometry.SheafedSpace.NativeCylinderLimit
end
end
