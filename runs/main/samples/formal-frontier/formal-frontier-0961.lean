@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

theorem isIso_iff_bijective_spec {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso f ↔ ∀ (R : Type u) [CommRing R],
      Function.Bijective (fun g : Spec (.of R) ⟶ X => g ≫ f) := by
  constructor
  · intro hf
    letI : IsIso f := hf
    intro R _
    constructor
    · intro g₁ g₂ h
      exact (cancel_mono f).mp h
    · intro h
      exact ⟨h ≫ inv f, by simp [Category.assoc]⟩
  · intro hf
    apply isDetecting_isAffine f
    intro G hG h
    letI : IsAffine G := hG
    have hR := hf Γ(G, ⊤)
    obtain ⟨g, hg, hg_unique⟩ :=
      (Function.bijective_iff_existsUnique _).mp hR (G.isoSpec.inv ≫ h)
    refine ⟨G.isoSpec.hom ≫ g, ?_, ?_⟩
    · simp only [Category.assoc, hg, Iso.hom_inv_id_assoc]
    · intro g' hg'
      apply (cancel_epi G.isoSpec.inv).mp
      simpa only [Iso.inv_hom_id_assoc] using
        hg_unique (G.isoSpec.inv ≫ g') (by simpa only [Category.assoc, hg'])

end AlgebraicGeometry.Scheme
end
