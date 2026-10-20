@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace

open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicTopology

/-- The last ambient term identifies with chains small in the ordered cover
`(U,V)`. -/
noncomputable def twoOpenUnionChainIso {X : TopCat.{u}} (U V : Opens X) :
    (twoOpenAmbientShortComplex U V).X₃ ≅
      smallSingularChainComplex (TopCat.twoOpenCover U V) :=
  ((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj integerCoefficients.{u}).mapIso
    (SSet.Subcomplex.eqToIso (TopCat.openSingularSet_sup U V))

end AlgebraicTopology
end
end
