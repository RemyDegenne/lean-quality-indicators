@[expose] public section

open List (Vector)

open Relation

open Nat (iterate)

open Function (update iterate_succ iterate_succ_apply iterate_succ' iterate_succ_apply'
  iterate_zero_apply)

open StateTransition

namespace Turing

namespace TM1

section

variable (Γ : Type*)

variable (Λ : Type*)

variable (σ : Type*)

open Stmt

variable {Γ Λ σ}

variable [Inhabited Λ]

/-- A set `S` of labels supports machine `M` if all the `goto`
  statements in the functions in `S` refer only to other functions
  in `S`. -/
def Supports (M : Λ → Stmt Γ Λ σ) (S : Finset Λ) :=
  default ∈ S ∧ ∀ q ∈ S, SupportsStmt S (M q)

end
end TM1
end Turing
end
