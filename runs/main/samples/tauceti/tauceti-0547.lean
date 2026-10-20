public section

open CategoryTheory

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X : Scheme.{u}}

namespace FiniteLocallyFreeSheaf.FixedRank

@[simp]
theorem toInvertible_map_hom (X : Scheme.{u})
    {E F : FiniteLocallyFreeSheaf.FixedRank X 1} (f : E ⟶ F) :
    ((toInvertible X).map f).hom =
      eqToHom (toInvertible_obj_obj X E) ≫ f.hom.hom ≫
        eqToHom (toInvertible_obj_obj X F).symm :=
  (rfl)

end FiniteLocallyFreeSheaf.FixedRank
end
end AlgebraicGeometry
end TauCeti
end
