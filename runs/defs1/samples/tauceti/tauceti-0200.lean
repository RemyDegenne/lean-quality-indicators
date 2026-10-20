public section

open scoped NNReal

namespace TauCeti

/-- The **generalized decreasing merge** of two sequences `a b : ℕ → ℝ≥0`: its `n`-th term is the
supremum of the thresholds `r` attained by at least `n + 1` distinct entries of the multiset union
of `a` and `b`, that is, by `Sum.elim a b` at `n + 1` distinct indices of `ℕ ⊕ ℕ`.

It is meaningful for bounded sequences; for antitone sequences it is computed by
`TauCeti.le_decreasingMerge_iff` and `TauCeti.decreasingMerge_lt_iff`. -/
noncomputable def decreasingMerge (a b : ℕ → ℝ≥0) (n : ℕ) : ℝ≥0 :=
  sSup {r | ∃ q : Fin (n + 1) → ℕ ⊕ ℕ, Function.Injective q ∧ ∀ i, r ≤ Sum.elim a b (q i)}

end TauCeti
end
