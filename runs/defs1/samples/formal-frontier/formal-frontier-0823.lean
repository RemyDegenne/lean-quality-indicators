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

variable (S : ιᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} C) (i0 : ι)

/-- The sections of the literal restricted tail stages over a named base open. -/
abbrev cylinderSections (W : Opens (S.obj (op i0))) : Set.Ici i0 ⥤ C :=
  (restricted S i0 W).rightOp ⋙ SheafedSpace.Γ

end AlgebraicGeometry.SheafedSpace.NativeCylinderLimit
end
end
