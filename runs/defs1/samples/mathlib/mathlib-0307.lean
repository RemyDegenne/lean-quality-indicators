@[expose] public section

open List (Vector)

open Relation

open Nat (iterate)

open Function (update iterate_succ iterate_succ_apply iterate_succ' iterate_succ_apply'
  iterate_zero_apply)

open StateTransition

namespace Turing

namespace TM0

section

variable (Γ : Type*)

variable (Λ : Type*)

/-- A Post-Turing machine with symbol type `Γ` and label type `Λ`
  is a function which, given the current state `q : Λ` and
  the tape head `a : Γ`, either halts (returns `none`) or returns
  a new state `q' : Λ` and a `Stmt` describing what to do,
  either a move left or right, or a write command.

  Both `Λ` and `Γ` are required to be inhabited; the default value
  for `Γ` is the "blank" tape value, and the default value of `Λ` is
  the initial state. -/
@[nolint unusedArguments] -- this is a deliberate addition, see comment
def Machine [Inhabited Λ] :=
  Λ → Γ → Option (Λ × (Stmt Γ))

end
end TM0
end Turing
end
