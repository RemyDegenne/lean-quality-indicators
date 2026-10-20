@[expose] public section

open CategoryTheory Opposite CountableCategory

variable (C : Type*) [Category* C] (J : Type*) [Countable J]

namespace CategoryTheory.Limits

universe v in

universe v in

section Preorder

namespace IsFiltered

attribute [local instance] IsFiltered.nonempty

variable {C} [Preorder J] [IsFiltered J]

theorem sequentialFunctor_map : Monotone (sequentialFunctor_obj J) :=
  monotone_nat_of_le_succ fun n ↦
    leOfHom (IsFilteredOrEmpty.cocone_objs ((exists_surjective_nat _).choose n)
      (sequentialFunctor_obj J n)).choose_spec.choose_spec.choose

end IsFiltered
end Preorder
end CategoryTheory.Limits
end
