@[expose] public section

open CategoryTheory Limits AlgebraicTopology

open scoped Simplicial

noncomputable section

namespace TopCat

universe u

open ContinuousMap

/-- A homotopy equivalence induces an isomorphism on reduced integer singular
homology in every nonnegative degree.

For the reduced-homology background see J. Peter May, *A Concise Course in Algebraic Topology*,
Chapter 14, §§1 and 3. This construction uses Mathlib's ordinary singular
homology (Joël Riou) and the project's augmentation-kernel model, not a
comparison with May's based-relative theory. -/
noncomputable def reducedSingularHomologyIsoOfHomotopyEquiv
    {X Y : TopCat.{u}} (e : (X : Type u) ≃ₕ (Y : Type u)) (n : ℕ) :
    reducedSingularHomology X n ≅ reducedSingularHomology Y n where
  hom := reducedSingularHomologyMap (TopCat.ofHom e.toFun) n
  inv := reducedSingularHomologyMap (TopCat.ofHom e.invFun) n
  hom_inv_id := by
    rw [← Functor.map_comp]
    have H : TopCat.Homotopy
        (TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun) (𝟙 X) :=
      e.left_inv.some
    change reducedSingularHomologyMap
      (TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun) n = _
    rw [reducedSingularHomologyMap_eq_of_homotopy H n]
    exact (reducedSingularHomologyFunctor n).map_id X
  inv_hom_id := by
    rw [← Functor.map_comp]
    have H : TopCat.Homotopy
        (TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun) (𝟙 Y) :=
      e.right_inv.some
    change reducedSingularHomologyMap
      (TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun) n = _
    rw [reducedSingularHomologyMap_eq_of_homotopy H n]
    exact (reducedSingularHomologyFunctor n).map_id Y

end TopCat
end
end
