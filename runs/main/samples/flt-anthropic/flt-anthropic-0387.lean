namespace P2MW.S_AlgebraicGeometry_flat_and_surjective_of_forall_exists_iso_morphismRestrict_eq_pullback_fst

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {S D B G : Scheme.{u}} (g : G ⟶ S) [Flat g] [Surjective g] (b : B ⟶ S) (π : D ⟶ B)
    (hloc : ∀ p : B, ∃ U : B.Opens, p ∈ U ∧
      ∃ e : (π ⁻¹ᵁ U : Scheme.{u}) ≅ pullback (U.ι ≫ b) g,
        e.hom ≫ pullback.fst (U.ι ≫ b) g = π ∣_ U) :
    Flat π ∧ Surjective π :=
  ⟨S1C.TorsorFlat.of_forall_exists_iso_morphismRestrict_eq_pullback_fst @Flat g ‹_› b π hloc,
    S1C.TorsorFlat.of_forall_exists_iso_morphismRestrict_eq_pullback_fst @Surjective g ‹_› b π hloc⟩

end P2MW.S_AlgebraicGeometry_flat_and_surjective_of_forall_exists_iso_morphismRestrict_eq_pullback_fst
