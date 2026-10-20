namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_forall_exists_opens_saturated_fppf_quotient_of_isAlgClosed

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

noncomputable section

namespace TranslateCoverGC3

variable {k : Type u} [CommRing k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)

theorem rt_mul (a b : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    rt L a ≫ rt L b = rt L (L.mul (𝟙 _) a b) := by
  have h1 : rt L a ≫ rt L b = (L.mul f (L.mul f RelativeGroupLaw.idPoint (const a f)) (const b f)).1 := by
    rw [← comp_rt L b f]; rfl
  rw [h1, L.mul_assoc]
  have h2 : L.mul f (const a f) (const b f) = const (L.mul (𝟙 _) a b) f := by
    simp only [const]
    rw [← L.mul_natural (𝟙 _) f f (Category.comp_id f)]
  rw [h2]; rfl

end TranslateCoverGC3
end
end P2MW.S_GoodReductionJacobian_RelativeGroupLaw_forall_exists_opens_saturated_fppf_quotient_of_isAlgClosed
