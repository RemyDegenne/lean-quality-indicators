public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (K : Type u) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (m : ℕ)

/-- The underlying over-scheme isomorphism induced by the coordinate
translation in Milne's *Algebraic Groups*, item 2.5; no group-law
compatibility is asserted for positive `m`. -/
def infinitesimalAdditiveTranslationIso :
    infinitesimalAdditiveUnderlyingScheme K p m ≅
      rootsOfUnityScheme K (p ^ m) :=
  (algSpec (.of K)).mapIso
    (CommAlgCat.isoMk (infinitesimalAdditiveTranslationAlgEquiv K p m)).op

end AlgebraicGeometry
end
end
