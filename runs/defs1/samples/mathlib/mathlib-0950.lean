@[expose] public section

open List (Vector)

open Relation

open Nat (iterate)

open Function (update iterate_succ iterate_succ_apply iterate_succ' iterate_succ_apply'
  iterate_zero_apply)

namespace Turing

namespace TM2to1

variable (K : Type*)

variable (Γ : K → Type*)

variable {Λ σ : Type*}

variable {K Γ}

variable (K Γ Λ σ)

variable {K Γ Λ σ}

open Λ'

open TM1.Stmt

section

open scoped Classical in
/-- The set of machine states accessible from an initial TM2 statement. -/
noncomputable def trStmts₁ : TM2.Stmt Γ Λ σ → Finset (Λ' K Γ Λ σ)
  | TM2.Stmt.push k f q => {go k (StAct.push f) q, ret q} ∪ trStmts₁ q
  | TM2.Stmt.peek k f q => {go k (StAct.peek f) q, ret q} ∪ trStmts₁ q
  | TM2.Stmt.pop k f q => {go k (StAct.pop f) q, ret q} ∪ trStmts₁ q
  | TM2.Stmt.load _ q => trStmts₁ q
  | TM2.Stmt.branch _ q₁ q₂ => trStmts₁ q₁ ∪ trStmts₁ q₂
  | _ => ∅

end
end TM2to1
end Turing
end
