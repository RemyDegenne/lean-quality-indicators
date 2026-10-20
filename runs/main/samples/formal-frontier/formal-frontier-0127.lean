@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory Polynomial

open scoped CategoryTheory.MonObj

universe u v w t

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K]

lemma rootsOfUnityCoordinateAlgEquiv_symm_root_isGroupLike
    (n : ℕ) [NeZero n] :
    IsGroupLikeElem K
      ((rootsOfUnityCoordinateAlgEquiv K n).symm
        (AdjoinRoot.root (rootsOfUnityPolynomial K n))) := by
  rw [rootsOfUnityCoordinateAlgEquiv_symm_root]
  exact AddMonoidAlgebra.isGroupLikeElem_single_one 1

end AlgebraicGeometry
end
end
