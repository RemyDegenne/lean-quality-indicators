@[expose] public section

universe w v v' u u'

namespace CategoryTheory

open Category HomotopicalAlgebra Limits SmallObject

variable {C : Type u} [Category.{v} C] (I : MorphismProperty C)

namespace SmallObject

open MorphismProperty

variable (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [I.IsCardinalForSmallObjectArgument κ]

include I κ

section

variable {X Y : C} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
lemma πObj_ιIteration_app_right :
    πObj I κ f ≫ ((ιIteration I κ).app f).right =
      ((iteration I κ).obj (Arrow.mk f)).hom := by simp [πObj]

end
end SmallObject
end CategoryTheory
end
