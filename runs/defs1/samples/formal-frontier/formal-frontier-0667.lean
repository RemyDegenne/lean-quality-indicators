@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace

open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicTopology

/-- Swapping the two members of the ordered difference/sum sequence.  The
intersection term is multiplied by `-1`, the middle term is braided, and the
union term is merely transported across commutativity of union. -/
noncomputable def subcomplexUnionSwapIso {X : SSet.{u}} (A B : X.Subcomplex) :
    subcomplexUnionShortComplex A B ≅ subcomplexUnionShortComplex B A :=
  ShortComplex.isoMk (-(subcomplexInfSwapChainIso A B))
    (biprod.braiding _ _) (subcomplexSupSwapChainIso A B)
    (by
      dsimp [subcomplexUnionShortComplex, CommSq.shortComplex,
        subcomplexInfSwapChainIso]
      apply biprod.hom_ext
      · simp [← Functor.map_comp]
        congr 1
      · simp [← Functor.map_comp]
        congr 1)
    (by
      dsimp [subcomplexUnionShortComplex, CommSq.shortComplex,
        subcomplexSupSwapChainIso]
      apply biprod.hom_ext'
      · simp [← Functor.map_comp]
        congr 1
      · simp [← Functor.map_comp]
        congr 1)

end AlgebraicTopology
end
end
