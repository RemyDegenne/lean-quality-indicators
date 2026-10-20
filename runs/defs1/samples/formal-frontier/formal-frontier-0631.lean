@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace

open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicTopology

/-- The difference map on homology, displayed with target
`Hₙ(U) ⊕ Hₙ(V)`. -/
noncomputable def twoOpenMayerVietorisFromIntersection {X : TopCat.{u}}
    (U V : Opens X) (n : ℕ) :
    ((twoOpenSmallShortComplex U V).X₁).homology n ⟶
      integralSingularHomology ((Opens.toTopCat X).obj U) n ⊞
        integralSingularHomology ((Opens.toTopCat X).obj V) n :=
  HomologicalComplex.homologyMap (twoOpenSmallShortComplex U V).f n ≫
    (twoOpenMiddleHomologyIso U V n).hom

end AlgebraicTopology
end
end
