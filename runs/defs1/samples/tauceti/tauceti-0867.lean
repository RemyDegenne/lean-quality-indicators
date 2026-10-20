public section

open CategoryTheory

namespace TauCeti.TorusCommHopfAlgCat

universe u

variable {k : Type u} [Field k]

/-- The cocharacter-lattice functor is the contragredient dual of the character-lattice functor.
This identifies the intrinsic geometric cocharacters with integral character functionals. -/
noncomputable def cocharacterLatticeFunctorIsoDual :
    cocharacterLatticeFunctor (k := k) ≅
      (characterLatticeFunctor (k := k)).op ⋙ GaloisLatticeCat.dualFunctor :=
  NatIso.ofComponents (fun T ↦ ObjectProperty.isoMk _
    (eqToIso (cocharacterLatticeFunctor_obj_obj T) ≪≫
      cocharacterRepresentationIsoDual T.unop ≪≫
      (eqToIso (congrArg Rep.dual (characterLatticeFunctor_obj_obj T.unop))).symm ≪≫
      (eqToIso (GaloisLatticeCat.dualFunctor_obj_obj _)).symm)) (fun {X Y} f ↦ by
    apply ObjectProperty.hom_ext
    dsimp
    simpa [cocharacterLatticeFunctor_map_hom, GaloisLatticeCat.dualFunctor_map_hom,
      characterLatticeFunctor_map_hom, Category.assoc] using
      congrArg (fun g ↦ eqToHom (cocharacterLatticeFunctor_obj_obj X) ≫ g ≫
        eqToHom (congrArg Rep.dual (characterLatticeFunctor_obj_obj Y.unop)).symm ≫
        eqToHom (GaloisLatticeCat.dualFunctor_obj_obj _).symm)
        (cocharacterRepresentationIsoDual_naturality f.unop))

end TauCeti.TorusCommHopfAlgCat
end
