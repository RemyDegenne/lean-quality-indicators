set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra GoodReductionJacobian

noncomputable section

namespace AlgebraicGeometry

namespace RelPicard

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {T T' : Scheme.{u}}
  {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}

def rigSectionPullbackSndPullbackIso (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (t : T ⟶ Spec (CommRingCat.of R))
    (D : T.Modules) :
    (Scheme.Modules.pullback (rigSection c t ε)).obj ((Scheme.Modules.pullback (pullback.snd c t)).obj D) ≅ D :=
  (Scheme.Modules.pullbackComp _ _).app D ≪≫ (Scheme.Modules.pullbackCongr (rigSection_snd ε t)).app D ≪≫
    (Scheme.Modules.pullbackId _).app D

end RelPicard
end AlgebraicGeometry
end
