public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace TauCeti

universe u

namespace PreAdicSpace

variable {X Y Z : PreAdicSpace.{u}}

section OfFac

variable {X Y Z : PreAdicSpace.{u}}

/-- A morphism of presheafed spaces `g` with `j ≫ g = i`, for morphisms `i : X ⟶ Z` and
`j : X ⟶ Y` of pre-adic spaces with `j` surjective on points, is a morphism of pre-adic spaces:
at `j x`, the stalk valuation of `Z` pulls back along the stalk maps of `g` and then of `j` to
the stalk valuation of `X` at `x`, and the stalk valuation of `Y` at `j x` is the pullback along
the stalk map of `j` alone. This is how morphisms out of a quotient such as
`PreAdicSpace.descend` are built. -/
def Hom.ofFacOfSurjective (i : X ⟶ Z) (j : X ⟶ Y)
    (g : Y.toPresheafedSpace ⟶ Z.toPresheafedSpace) (hj : Function.Surjective j.base)
    (h : j.toHom ≫ g = i.toHom) : Y ⟶ Z where
  toHom := g
  stalkValuation_eq y := by
    obtain ⟨x, rfl⟩ := hj y
    obtain ⟨i, hi⟩ := i
    have h' : j.toHom ≫ g = i := h
    subst h'
    -- the stalk map of `j ≫ g` at `x` is the stalk map of `g` at `j x` followed by that of `j`
    have hcomp : (toRingPresheafedSpaceHom (j.toHom ≫ g)).stalkMap x =
        (toRingPresheafedSpaceHom g).stalkMap (j.base x) ≫
          (toRingPresheafedSpaceHom j.toHom).stalkMap x := by
      rw [PresheafedSpace.stalkMap.congr_hom (toRingPresheafedSpaceHom (j.toHom ≫ g))
        (toRingPresheafedSpaceHom j.toHom ≫ toRingPresheafedSpaceHom g)
        (CategoryTheory.Functor.map_comp _ _ _) x,
        PresheafedSpace.stalkMap.comp (toRingPresheafedSpaceHom j.toHom)
          (toRingPresheafedSpaceHom g) x]
      -- the `eqToHom` relates two stalks at base points which are definitionally `g (j x)`
      exact (congrArg (· ≫ _) (eqToHom_refl _ _)).trans (Category.id_comp _)
    -- as in `Hom.ofFac`, the base point of `hi x` is definitionally `g.base (j.base x)` but cannot
    -- be rewritten to it, since it occurs in the types of both sides
    exact (hi x).trans ((congrArg (fun f ↦ ValuationSpectrum.comap f.hom (X.stalkValuation x))
      hcomp).trans ((ValuationSpectrum.comap_hom_comap_hom _ _ _).symm.trans
        (congrArg (ValuationSpectrum.comap _) (j.stalkValuation_eq x).symm)))

end OfFac
end PreAdicSpace
end TauCeti
end
