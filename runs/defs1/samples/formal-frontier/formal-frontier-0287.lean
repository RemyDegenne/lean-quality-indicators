public section

open CategoryTheory

namespace FiniteGroupTateCohomology

universe u v w

variable {R : Type u} {G : Type v} [CommRing R] [Group G] [Fintype G]

/-- The norm from coinvariants to invariants, natural in the representation. -/
@[expose]
noncomputable def normNatTrans :
    Rep.coinvariantsFunctor R G ⟶ Rep.invariantsFunctor R G where
  app := normFromCoinvariants
  naturality _ _ f := (normFromCoinvariants_naturality f).symm

end FiniteGroupTateCohomology
end
