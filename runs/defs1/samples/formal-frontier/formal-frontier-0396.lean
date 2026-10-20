@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace

open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicTopology

/-- The ordinary/open-chain short complex identified with its ambient
subcomplex model. -/
noncomputable def twoOpenSmallToAmbientIso {X : TopCat.{u}} (U V : Opens X) :
    twoOpenSmallShortComplex U V ≅ twoOpenAmbientShortComplex U V :=
  ShortComplex.isoMk (twoOpenIntersectionChainIso U V)
    (twoOpenBiprodChainIso U V) (twoOpenUnionChainIso U V).symm
    (by simp [twoOpenSmallShortComplex])
    (by simp [twoOpenSmallShortComplex])

end AlgebraicTopology
end
end
