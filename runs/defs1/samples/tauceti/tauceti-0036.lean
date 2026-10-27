public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

section OpenImmersion

variable {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]

/-- The morphism of sheaves of rings along `j.opensFunctor`, given on sections by the inverses of
the isomorphisms `Scheme.Hom.appIso`, along which `Scheme.Modules.restrictFunctor j` is the
pushforward of sheaves of modules. -/
-- Exposed because the exported instance `restrictFunctorLaxMonoidal` is checked by unfolding
-- `restrictFunctor j` to the pushforward along this morphism.
@[expose]
def restrictRingCatSheafHom :
    U.ringCatSheaf ⟶ (j.opensFunctor.sheafPushforwardContinuous _ _ _).obj Y.ringCatSheaf :=
  letI α : U.presheaf ⟶ j.opensFunctor.op ⋙ Y.presheaf := { app W := (j.appIso W.unop).inv }
  ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩

end OpenImmersion
end
end AlgebraicGeometry.Scheme.Modules
end
