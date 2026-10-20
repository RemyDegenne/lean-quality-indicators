namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange

set_option autoImplicit false

universe u v w

p2m_open

p2m_open

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace GoodReductionJacobian

namespace RelativeGroupLaw

namespace BCImage

p2m_open

section GroupLaw

variable {R R' : Type u} [CommRing R] [CommRing R']
  (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)) [Mono ι] [Flat ι] [QuasiCompact ι] [IsSchemeTheoreticallyDominant ι]
  {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
  {X : Scheme.{u}} {g : X ⟶ Spec (CommRingCat.of R')} [Flat g] (LX : RelativeGroupLaw R' g)
  (σ : SchemeHomOver g (pullback.snd f ι))
  [QuasiCompact (σ.1 ≫ pullback.fst f ι)] [Flat ((σ.1 ≫ pullback.fst f ι).imageι ≫ f)]
  (hσ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver t g),
      NeronModelInfra.schemeHomOverComp (LX.mul t x y) σ =
        (L.baseChange ι).mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ))

noncomputable def onePt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : SchemeHomOver t ((τ ι σ).imageι ≫ f) :=
  ⟨t ≫ oneB ι L LX σ hσ, by
    rw [Category.assoc, ← Category.assoc (oneB ι L LX σ hσ), oneB_imageι, oneMor_over L, Category.comp_id]⟩

end GroupLaw
end BCImage
end RelativeGroupLaw
end GoodReductionJacobian
end P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange
