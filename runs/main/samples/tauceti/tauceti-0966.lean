public section

open CategoryTheory AlgebraicGeometry Opposite

open scoped CategoryTheory.MonObj

namespace TauCeti

universe u

namespace FiniteLocallyFreeCommAffineGroupSchemeCat

open finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat

@[simp]
theorem cartierDuality_functor (R : Type u) [CommRing R] :
    (cartierDuality R).functor =
      (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
        R).rightOp.inverse ⋙
        (FiniteLocallyFreeBicommutativeHopfAlgCat.dualFunctor (k := R)).rightOp ⋙
        (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
          R).functor :=
  (rfl)

end FiniteLocallyFreeCommAffineGroupSchemeCat
end TauCeti
end
