public section

open CategoryTheory CategoryTheory.Limits

namespace FiniteGroupTateCohomology

universe u

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- The natural norm, regarded as a functor to the arrow category. -/
@[expose]
noncomputable def normArrowFunctor : Rep R G ⥤ Arrow (ModuleCat R) where
  obj M := Arrow.mk (normFromCoinvariants M)
  map {M N} f := Arrow.homMk
    ((Rep.coinvariantsFunctor R G).map f)
    ((Rep.invariantsFunctor R G).map f)
    (normFromCoinvariants_naturality f).symm

end FiniteGroupTateCohomology
end
