namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Complexity.FiniteComposition

open Turing Function Finset Polynomial

open Binary (Trace)

attribute [instance] Machine.decK Machine.finK Machine.finΓ Machine.finLabel Machine.finState

namespace Embedding

variable {K K' L S L' S' : Type} [DecidableEq K] [DecidableEq K']
  {Γ : K → Type} {Γ' : K' → Type}

variable (E : Embedding Γ L S Γ' L' S')

theorem stepAux_stmt (q : TM2.Stmt Γ L S) (v : S) (s : ∀ k, List (Γ k)) :
    TM2.stepAux (E.stmt q) (E.state v) (E.stack s) = E.cfg (TM2.stepAux q v s) := by
  induction q generalizing v s with
  | push k f q ih =>
      simp only [stmt, TM2.stepAux, E.read_state, E.stack_key, ← List.map_cons,
        ← E.stack_update]
      exact ih _ _
  | peek k f q ih =>
      simp only [stmt, TM2.stepAux, E.read_state, E.stack_key, head_map_inverse, E.write_state]
      exact ih _ _
  | pop k f q ih =>
      simp only [stmt, TM2.stepAux, E.read_state, E.stack_key, head_map_inverse,
        E.write_state, ← List.map_tail, ← E.stack_update]
      exact ih _ _
  | load f q ih =>
      simp only [stmt, TM2.stepAux, E.read_state, E.write_state]
      exact ih _ _
  | branch f q r ihq ihr =>
      cases h : f v <;> simp only [stmt, TM2.stepAux, E.read_state, h, Bool.cond_false,
        Bool.cond_true]
      · exact ihr _ _
      · exact ihq _ _
  | goto f => simp only [stmt, TM2.stepAux, E.read_state, cfg, Option.elim_some]
  | halt => exact E.stop_spec v s

end Embedding
end MetricKMedian.Complexity.FiniteComposition
end Inline_PCPInherited
end OAI
