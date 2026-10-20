@[expose] public section

open Relation

open scoped List

universe u v w

variable {α : Type u}

attribute [local simp] List.append_eq_has_append

namespace FreeGroup

variable {L L₁ L₂ L₃ : List (α × Bool)}

@[to_additive]
theorem one_eq_mk : (1 : FreeGroup α) = mk [] :=
  rfl

end FreeGroup
end
