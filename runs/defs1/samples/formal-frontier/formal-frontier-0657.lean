@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace

open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicTopology

/-- The ordered chain sum induced by the inclusions of `U` and `V` into `X`. -/
def twoOpenSumChainMap {X : TopCat.{u}} (U V : Opens X) :
    integralSingularChains ((Opens.toTopCat X).obj U) ⊞
        integralSingularChains ((Opens.toTopCat X).obj V) ⟶
      integralSingularChains X :=
  biprod.desc (integralSingularChainMap U.inclusion')
    (integralSingularChainMap V.inclusion')

end AlgebraicTopology
end
end
