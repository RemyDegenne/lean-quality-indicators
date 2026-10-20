namespace P2MW.S_CerednikDrinfeld_QM_exists_pt_eq_ptF_comp_of_isFineModuli_of_forall_ptF_comp_eq

set_option autoImplicit false

p2m_open

open scoped Quaternion TensorProduct

noncomputable section

namespace P2mKcFppfPt

section Descent

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ} {𝒪 : Type} [CommRing 𝒪]
  {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
  {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
    FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
  (hM : IsFineModuli Λ N m M πM ptF) {X : Scheme.{0}} (π : M ⟶ X)
  (hinvP : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
    (E : FakeEllipticCurve Λ N S) (P P' : E.FullLevel m), (ptF S s ⟨E, P'⟩).1 ≫ π = (ptF S s ⟨E, P⟩).1 ≫ π)

attribute [scoped instance] Cover.inst

variable {S : Type} [CommRing S]

scoped instance epi_cover {E : FakeEllipticCurve Λ N S} (c : Cover m S E) : Epi (Spec.map (CommRingCat.ofHom c.φ)) := by
  haveI := flat_of_faithfullyFlat c.ff
  haveI := surjective_of_faithfullyFlat c.ff
  infer_instance

include hM hinvP in

theorem descent_condition (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) {E : FakeEllipticCurve Λ N S}
    (c : Cover m S E) {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ Spec (CommRingCat.of c.S'))
    (h : g₁ ≫ Spec.map (CommRingCat.ofHom c.φ) = g₂ ≫ Spec.map (CommRingCat.ofHom c.φ)) :
    g₁ ≫ (ptF c.S' (Spec.map (CommRingCat.ofHom c.φ) ≫ s) c.u').1 ≫ π =
      g₂ ≫ (ptF c.S' (Spec.map (CommRingCat.ofHom c.φ) ≫ s) c.u').1 ≫ π := by
  apply Scheme.Cover.hom_ext Z.affineCover
  intro i
  rw [← Category.assoc, ← Category.assoc (Z.affineCover.f i)]
  exact descent_affine hM π hinvP s c (Z.affineCover.f i ≫ g₁) (Z.affineCover.f i ≫ g₂)
    (by simp only [Category.assoc, h])

end Descent
end P2mKcFppfPt
end
end P2MW.S_CerednikDrinfeld_QM_exists_pt_eq_ptF_comp_of_isFineModuli_of_forall_ptF_comp_eq
