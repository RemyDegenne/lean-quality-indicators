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

/-- The original diagram, restricted to the opposite principal tail. -/
abbrev tailDiagram : (Set.Ici i0)ᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} C :=
  (tailInclusion i0).op ⋙ N

end AlgebraicGeometry.SheafedSpace.NativeCylinderLimit
end
end
