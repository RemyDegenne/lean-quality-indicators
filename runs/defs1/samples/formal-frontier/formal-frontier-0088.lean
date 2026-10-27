set_option warningAsError true

public section

open CategoryTheory

universe u

attribute [instance] CompHausAddCommGrp.addCommGroup
  CompHausAddCommGrp.isTopologicalAddGroup

namespace CompHausAddCommGrp

/-- A closed additive subgroup of a compact Hausdorff additive commutative
group is again a compact Hausdorff additive commutative group. -/
noncomputable abbrev ofClosedAddSubgroup (A : CompHausAddCommGrp.{u})
    (H : ClosedAddSubgroup A) : CompHausAddCommGrp.{u} := by
  let _ : CompactSpace H.toAddSubgroup :=
    isCompact_iff_compactSpace.mp H.isClosed'.isCompact
  exact of H.toAddSubgroup

end CompHausAddCommGrp
end
