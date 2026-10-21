namespace OAI

namespace DirectedFeedback.BoundedExpr

open StackDSL StackDSL.Code StackDSL.Ops

namespace Expr

theorem correct_lit {r : Nat} (n : Nat) : Correct (Expr.lit (r := r) n) := by
  intro L x a s h
  exact pushN_run L.output n s

end Expr
end DirectedFeedback.BoundedExpr
end OAI
