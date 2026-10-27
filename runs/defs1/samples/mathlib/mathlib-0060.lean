@[expose] public section

universe w v v' u u'

namespace CategoryTheory

open Category Limits

namespace SmallObject

variable {C : Type u} [Category.{v} C] {J : Type w}

section

variable [PartialOrder J] {j : J} (F : Set.Iic j ⥤ C) {i : J} (hi : i ≤ j)

/-- The functor `Set.Iic i ⥤ C` obtained by "restriction" of `F : Set.Iic j ⥤ C`
when `i ≤ j`. -/
def restrictionLE : Set.Iic i ⥤ C :=
  (Set.initialSegIicIicOfLE hi).monotone.functor ⋙ F

end
end SmallObject
end CategoryTheory
end
