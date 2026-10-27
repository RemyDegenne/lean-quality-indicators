set_option warningAsError true

public section

open CategoryTheory

universe u

attribute [instance] CompHausAddCommGrp.addCommGroup
  CompHausAddCommGrp.isTopologicalAddGroup

namespace CompHausAddCommGrp

/-- The compact Hausdorff group carried by the kernel of a continuous additive
homomorphism. -/
noncomputable abbrev kernelGroup {A B : CompHausAddCommGrp.{u}} (f : A ⟶ B) :
    CompHausAddCommGrp.{u} :=
  ofClosedAddSubgroup A (kernelClosedAddSubgroup f)

end CompHausAddCommGrp
end
