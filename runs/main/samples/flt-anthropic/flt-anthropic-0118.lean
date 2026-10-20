namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_isLevelIsogeny

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

universe u

namespace IMGSUB

variable {R : Type u} [CommRing R]
  {A₀ A : Scheme.{u}} {f₀ : A₀ ⟶ Spec (CommRingCat.of R)} {f : A ⟶ Spec (CommRingCat.of R)}
  (L₀ : RelativeGroupLaw R f₀) (L : RelativeGroupLaw R f)
  (p : A₀ ⟶ A) (hp : p ≫ f = f₀)
  (hp_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f₀),
    mapPt p hp (L₀.mul t P Q) = L.mul t (mapPt p hp P) (mapPt p hp Q))
  {C₀ : Scheme.{u}} (ι : C₀ ⟶ A₀)
  (hsub : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f₀),
    FactorsThrough ι P → FactorsThrough ι Q → FactorsThrough ι (L₀.mul t P Q) ∧ FactorsThrough ι (L₀.inv t P))
  (hdisj : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f₀),
    FactorsThrough ι P → mapPt p hp P = L.one t → P = L₀.one t)

theorem factorsThrough_iff {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (Q : SchemeHomOver t f) :
    FactorsThrough (ι ≫ p) Q ↔ ∃ P : SchemeHomOver t f₀, FactorsThrough ι P ∧ mapPt p hp P = Q := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨⟨c ≫ ι, by rw [← hp, Category.assoc, ← Category.assoc ι, ← Category.assoc, hc]; exact Q.2⟩, ⟨c, rfl⟩, ?_⟩
    apply Subtype.ext; simp only [mapPt, Category.assoc]; simpa [Category.assoc] using hc
  · rintro ⟨P, ⟨c, hc⟩, rfl⟩
    exact ⟨c, by simp only [mapPt, ← Category.assoc, hc]⟩

end IMGSUB
end P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_isLevelIsogeny
