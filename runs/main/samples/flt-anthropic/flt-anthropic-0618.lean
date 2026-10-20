namespace P2MW.S_groupCohomology_exists_isLocalBridge1

set_option autoImplicit false

open CategoryTheory groupCohomology

namespace LB1EX

variable {k : Type} [CommRing k] {H : Type} [Group H] {D : Type} [Group D] (π : H →* D)
  {R P B : Rep.{0} k D} (f : R ⟶ P) (g : P ⟶ B)
  {X : Rep.{0} k D} {A : Rep.{0} k H} (ι : X →+ A)
  {p : ℕ} {M : Rep.{0} (ZMod p) H} (κ : B →+ M →+ A)

section hyps

variable (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom)
  (hιeq : ∀ (h : H) (x : X), ι (X.ρ (π h) x) = A.ρ h (ι x))
  (hκeq : ∀ (h : H) (b : B) (m : M), κ (B.ρ (π h) b) (M.ρ h m) = A.ρ h (κ b m))
  (hκ : ∀ c : B →+ A, ∃! m : M, ∀ b, κ b m = c b)

include hfg hg hκ hιeq in
lemma κ_nOf (φ : R ⟶ X) (ψ : (ihom (Rep.res π P)).obj A) (hψ : ∀ x : R, ev π ψ (f.hom x) = ι (φ.hom x)) (h : H) (x : P) :
    κ (g.hom x) (nOf π g κ ψ h) = cob π ψ h x := by
  classical
  have hex : ∃ m : M, ∀ x : P, κ (g.hom x) m = cob π ψ h x :=
    exists_forall_κ_eq f g κ hfg hg hκ (cob π ψ h) (cob_apply_f π f ι hιeq φ ψ hψ h)
  simp only [nOf, dif_pos hex]
  exact hex.choose_spec x

end hyps
end LB1EX
end P2MW.S_groupCohomology_exists_isLocalBridge1
