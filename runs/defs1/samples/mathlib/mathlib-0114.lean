@[expose] public section

open List (Vector)

open Relation

open Nat (iterate)

open Function (update iterate_succ iterate_succ_apply iterate_succ' iterate_succ_apply'
  iterate_zero_apply)

namespace Turing

namespace TM2

variable {K : Type*}

variable (Γ : K → Type*)

variable (Λ : Type*)

variable (σ : Type*)

open Stmt

variable {Γ Λ σ}

section

variable [DecidableEq K]

/-- The (reflexive) reachability relation for the TM2 model. -/
def Reaches (M : Λ → Stmt Γ Λ σ) : Cfg Γ Λ σ → Cfg Γ Λ σ → Prop :=
  ReflTransGen fun a b ↦ b ∈ step M a

end
end TM2
end Turing
end
