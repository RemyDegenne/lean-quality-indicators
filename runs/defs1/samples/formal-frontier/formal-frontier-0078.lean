@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory Polynomial

open scoped CategoryTheory.MonObj

universe u v w t

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K]

/-- The distinguished root in `AdjoinRoot (X ^ n - 1)` as an `n`-th root of
unity. -/
def adjoinRootRootsOfUnity (n : ℕ) [NeZero n] :
    rootsOfUnity n (AdjoinRoot (rootsOfUnityPolynomial K n)) :=
  rootsOfUnity.mkOfPowEq (AdjoinRoot.root (rootsOfUnityPolynomial K n)) (by
    have h : AdjoinRoot.root (rootsOfUnityPolynomial K n) ^ n - 1 = 0 := by
      simpa [rootsOfUnityPolynomial] using
        AdjoinRoot.eval₂_root (rootsOfUnityPolynomial K n)
    exact sub_eq_zero.mp h)

end AlgebraicGeometry
end
end
