public section

universe w v v' u u'

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]

namespace Equivalence

variable (e : C ≌ D)

include e

lemma isAccessibleCategory [IsAccessibleCategory.{w} C] :
    IsAccessibleCategory.{w} D := by
  obtain ⟨κ, _, _⟩ := IsAccessibleCategory.exists_cardinal.{w} C
  exact ⟨κ, inferInstance, e.isCardinalAccessibleCategory κ⟩

end Equivalence
end CategoryTheory
end
