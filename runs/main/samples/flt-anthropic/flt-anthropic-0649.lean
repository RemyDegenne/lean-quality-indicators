namespace P2MW.S_AlgebraicGeometry_Etale_of_forall_pullback_snd_localization_atPrime

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation g]
    (H : ∀ (p : Ideal R) [p.IsPrime],
      Etale (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p)))))) :
    Etale g := by
  haveI : Flat g := AlgebraicGeometry.Flat.of_forall_pullback_snd_localization_atPrime g
    (fun p _ => by haveI := H p; infer_instance)
  haveI : FormallyUnramified g := AlgebraicGeometry.FormallyUnramified.of_forall_pullback_snd_localization_atPrime g
    (fun p _ => by haveI := H p; infer_instance)
  exact Etale.of_formallyUnramified_of_flat g

end P2MW.S_AlgebraicGeometry_Etale_of_forall_pullback_snd_localization_atPrime
