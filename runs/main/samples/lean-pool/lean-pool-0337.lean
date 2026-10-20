@[expose] public section

namespace BSLambda

open scoped Matrix Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem gram_ne_zero_iff {f : Input V → Bool} {x y : Ones f} :
    gram f x y ≠ 0 ↔ ∃ z : Zeros f, hammingDist x.1 z.1 = 1 ∧ hammingDist y.1 z.1 = 1 := by
  rw [gram_apply, Nat.cast_ne_zero, Finset.card_ne_zero, Finset.filter_nonempty_iff]
  simp

end BSLambda
end
