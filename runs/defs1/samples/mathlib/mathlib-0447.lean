@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₁' u₂ u₃

set_option linter.translate.warnInvalid false in
/-- The only morphisms in `Discrete α` are the identity morphisms. -/
@[nolint structureInType, to_dual self (reorder := a b) (relevant_arg := _)]
structure Discrete.Hom {α : Type u₁} (a b : α) : Type u₁ where
  eq : a = b

end CategoryTheory
end
