namespace OAI

section

open scoped BigOperators

namespace ExactQuantumFactoring.OrderTrial.Expressions

variable {v : Type*}

open RatExpr

lemma dynamicRamp_correct (x : v → ℕ) (q : IntExpr v) (a : ℤ) :
    (dynamicRamp q a).eval x=rampPiece (q.eval x) a := by
  by_cases h : a ≤ q.eval x <;> simp [dynamicRamp,rampPiece,h,PolyExpr.eval]

end ExactQuantumFactoring.OrderTrial.Expressions
end
end OAI
