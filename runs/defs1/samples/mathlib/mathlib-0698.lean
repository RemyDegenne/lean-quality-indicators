@[expose] public section

namespace CategoryTheory

open Category Opposite

universe w v u

variable {C : Type u} [Category.{v} C] {A : Cᵒᵖ ⥤ Type v}

namespace OverPresheafAux

namespace OverArrows

/-- Since `OverArrows η s` can be thought of to contain certain morphisms `yoneda.obj X ⟶ F`, the
Yoneda lemma yields elements `F.obj (op X)`. -/
def val {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A} :
    OverArrows η s → F.obj (op X) :=
  Subtype.val

end OverArrows
end OverPresheafAux
end CategoryTheory
end
