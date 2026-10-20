@[expose] public section

open Lean Meta Elab Tactic

elab (name := mfldSetTac) "mfld_set_tac" : tactic => withMainContext do
  let g ← getMainGoal
  let goalTy := (← instantiateMVars (← g.getDecl).type).getAppFnArgs
  match goalTy with
  | (``Eq, #[_ty, _e₁, _e₂]) =>
    evalTactic (← `(tactic| (
      apply Set.ext; intro my_y
      constructor <;>
        · intro h_my_y
          try simp only [*, mfld_simps] at h_my_y
          try simp only [*, mfld_simps])))
  | (``LE.le, #[_ty, _inst, _e₁, _e₂]) =>
    evalTactic (← `(tactic| (
      intro my_y h_my_y
      try simp only [*, mfld_simps] at h_my_y
      try simp only [*, mfld_simps])))
  | _ => throwError

open Function Set

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

namespace PartialEquiv

variable (e : PartialEquiv α β) (e' : PartialEquiv β γ)

theorem EqOnSource.source_eq {e e' : PartialEquiv α β} (h : e ≈ e') : e.source = e'.source :=
  h.1

end PartialEquiv
end
