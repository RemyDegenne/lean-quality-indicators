@[expose] public section

namespace GaleStewartGame

elab "casesPlayer" : tactic => withMainContext do
  for hyp in ← getLCtx do
    if ← isDefEq (← instantiateMVars hyp.type) q(Player) then
      let syn ← exprToSyntax hyp.toExpr
      evalTactic (← `(tactic | cases $syn:term))
      return
  throwError

macro "casesPlayers" : tactic => `(tactic | focus repeat all_goals casesPlayer)

macro "synthIsPosition" : tactic =>
  `(tactic | first | done |
  (casesPlayers <;> (try apply_fun List.length at *) <;>
    simpAtStar (config := {failIfUnchanged := false}) only [simp_isPosition, simp_lengths] <;>
    /-(try split_ifs at * <;>
      --split_ifs at * fails in win_asap due to order issue
      --(manually reordering goals fixes the issue)
      simpAtStar (config := {failIfUnchanged := false}) only [simp_isPosition]) <;>-/
    omega))

variable {A : Type*} (x : List A) (p q : Player)

namespace Player

@[simp] lemma residual_even (h : x.length % 2 = 0) :
  p.residual x = p := by synthIsPosition

end Player
end GaleStewartGame
end
