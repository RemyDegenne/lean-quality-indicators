@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory Polynomial

open scoped CategoryTheory.MonObj

universe u v w t

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K]

lemma adjoinRootToRootsOfUnityCoordinate_comp_coordinateTo (n : ℕ)
    [NeZero n] :
    (adjoinRootToRootsOfUnityCoordinate K n).comp
      (rootsOfUnityCoordinateToAdjoinRoot K n) =
        AlgHom.id K (rootsOfUnityCoordinateRing K n) := by
  apply AddMonoidAlgebra.algHom_ext
  · intro x
    rw [← ZMod.natCast_zmod_val x]
    change ((adjoinRootToRootsOfUnityCoordinate K n).comp
        (rootsOfUnityCoordinateToAdjoinRoot K n))
          (AddMonoidAlgebra.single (x.val : ZMod n) 1) =
      (AlgHom.id K (rootsOfUnityCoordinateRing K n))
        (AddMonoidAlgebra.single (x.val : ZMod n) 1)
    rw [show AddMonoidAlgebra.single (x.val : ZMod n) (1 : K) =
        rootsOfUnityCoordinateGenerator K n ^ x.val by
      simp [rootsOfUnityCoordinateGenerator]]
    simp
  · ext

end AlgebraicGeometry
end
end
