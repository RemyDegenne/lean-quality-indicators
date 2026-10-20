set_option warningAsError true

public section

open CategoryTheory

universe u

attribute [instance] CompHausAddCommGrp.addCommGroup
  CompHausAddCommGrp.isTopologicalAddGroup

namespace CompHausAddCommGrp

/-- The canonical projection to the compact Hausdorff quotient by the range. -/
@[expose] noncomputable def quotientRangeπ {A B : CompHausAddCommGrp.{u}} (f : A ⟶ B) :
    B ⟶ quotientRange f :=
  ConcreteCategory.ofHom
    { toAddMonoidHom := QuotientAddGroup.mk' f.hom.range
      continuous_toFun := QuotientAddGroup.continuous_mk }

end CompHausAddCommGrp
end
