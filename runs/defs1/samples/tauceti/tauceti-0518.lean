public section

open CategoryTheory AlgebraicGeometry Opposite

open scoped CategoryTheory.MonObj

namespace TauCeti

universe u

namespace
  finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat

/-- The object produced by the finite-locally-free Hopf/group-scheme anti-equivalence is
its bundled Hopf spectrum. -/
noncomputable def functorObjIso (R : Type u) [CommRing R]
    (H : (FiniteLocallyFreeBicommutativeHopfAlgCat.{u} R)ᵒᵖ) :
    (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
        R).functor.obj H ≅
      ⟨⟨(hopfSpec (CommRingCat.of R)).obj (op H.unop.obj), by
          rw [affineGroupSchemeProperty_iff, hopfSpec_obj_X_left]
          infer_instance⟩, by
        have hH := (finiteLocallyFreeBicommutativeHopfAlgProperty_iff R H.unop.obj).mp
          H.unop.property
        let _ : Module.Finite R H.unop.obj := hH.1
        have hp := (moduleProjective_iff_flat_and_locallyOfFinitePresentation_hopfSpec
          R H.unop.obj).mp hH.2.1
        exact ⟨(moduleFinite_iff_isFinite_hopfSpec R H.unop.obj).mp
          hH.1, hp.1, hp.2,
          (isCocomm_iff_isCommMonObj_hopfSpec R H.unop.obj).mp hH.2.2⟩⟩ :=
  (finiteLocallyFreeCommAffineGroupSchemeProperty (CommRingCat.of R)).ι.preimageIso
    ((affineGroupSchemeProperty (CommRingCat.of R)).ι.preimageIso
      ((functorCompιIso R).app H))

end finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
end TauCeti
end
