set_option warningAsError true

@[expose] public section

open scoped Matrix

namespace Matrix

universe u

/-- The matrix of the first-coordinate completion of a unimodular row, in
the matrix-completion formulation of Weibel, *The K-book*, I.1.3. -/
noncomputable def coefficientRowCompletionOfStableRangeCondition
    (R : Type u) [CommRing R] (n : ℕ) (a : Fin (n + 1) → R)
    (ha : Bass.IsRightUnimodular a) {s : ℕ}
    (hs : Bass.StableRangeCondition R s) (hsn : s ≤ n) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  LinearMap.toMatrix'
    (LinearEquiv.coefficientRowCompletionOfStableRangeCondition R n a ha hs hsn).toLinearMap

end Matrix
end
