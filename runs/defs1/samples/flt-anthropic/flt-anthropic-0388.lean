set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

open scoped Quaternion

namespace CerednikDrinfeld.QM

namespace FakeEllipticCurve

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

def WithFullLevel.IsTwist {S : Type u} [CommRing S] {m : ℕ} (c : ↥Λ) (u u' : WithFullLevel Λ N m S) : Prop :=
  ∃ (e : u.1.A ≅ u'.1.A) (he : e.hom ≫ u'.1.f = u.1.f),
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f),
      mapPt e.hom he (u.1.L.mul t P Q) = u'.1.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
    (∀ x : ↥Λ, u.1.act x ≫ e.hom = e.hom ≫ u'.1.act x) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.1.lev P ↔ FactorsThrough u'.1.lev (mapPt e.hom he P)) ∧
    mapPt e.hom he (pushPt (u.1.act c) (u.1.act_over c) u.2.P) = u'.2.P

end FakeEllipticCurve
end CerednikDrinfeld.QM
end
