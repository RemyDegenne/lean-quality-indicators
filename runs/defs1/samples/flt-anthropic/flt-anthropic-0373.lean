namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isPullback_of_isPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

open CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve

open scoped Quaternion

namespace ALBaseChange

variable {S S' : Type} [CommRing S] [CommRing S'] {φ : S →+* S'}

section Square

variable {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S')} {g : A' ⟶ A}

def img (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))) {T : Scheme.{0}}
    {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' f') :
    SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) f :=
  ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩

end Square
end ALBaseChange
end P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isPullback_of_isPullback
