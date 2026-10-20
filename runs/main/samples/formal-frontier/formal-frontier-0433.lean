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

theorem tailDirectedOrder (i0 : ι) : IsDirectedOrder (Set.Ici i0) :=
  tailDirected i0

end AlgebraicGeometry.SheafedSpace.NativeCylinderLimit
end
end
