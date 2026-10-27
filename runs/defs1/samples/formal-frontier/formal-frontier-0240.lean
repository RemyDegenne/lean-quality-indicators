set_option warningAsError true

public section

open CategoryTheory

universe u

attribute [instance] CompHausAddCommGrp.addCommGroup
  CompHausAddCommGrp.isTopologicalAddGroup

namespace CompHausAddCommGrp

/-- The quotient by a closed additive subgroup, with its quotient topology. -/
noncomputable abbrev quotient (A : CompHausAddCommGrp.{u})
    (H : ClosedAddSubgroup A) : CompHausAddCommGrp.{u} := by
  let _ : IsClosed (H.toAddSubgroup : Set A) := H.isClosed'
  exact of (A ⧸ H.toAddSubgroup)

end CompHausAddCommGrp
end
