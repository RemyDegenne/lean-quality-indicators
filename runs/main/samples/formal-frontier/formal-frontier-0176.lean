set_option warningAsError true

public section

open CategoryTheory

universe u

attribute [instance] CompHausAddCommGrp.addCommGroup
  CompHausAddCommGrp.isTopologicalAddGroup

namespace CompHausAddCommGrp

@[simp]
lemma coe_of (A : Type u) [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [CompactSpace A] [T2Space A] :
    (of A : Type u) = A :=
  rfl

end CompHausAddCommGrp
end
