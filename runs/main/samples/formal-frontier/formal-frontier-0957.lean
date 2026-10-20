@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.EquivalenceRelation

universe u

variable {R X : Scheme.{u}} {p₁ p₂ : R ⟶ X}
  [Flat p₁] [IsFinite p₁] [LocallyOfFinitePresentation p₁] [IsAffine X]

lemma finrankOpen_equalizer_isLocalizationAway_of_basicOpen_eq
    (h : CategoryTheory.EquivalenceRelation p₁ p₂) (r : ℕ)
    (e : AlgHom.equalizer p₁.appTop.hom.toIntAlgHom
      p₂.appTop.hom.toIntAlgHom)
    (he : IsIdempotentElem e)
    (hbasic : X.basicOpen e.1 = finrankOpen (p₁ := p₁) r) :
    let U := finrankOpen (p₁ := p₁) r
    let V := p₁ ⁻¹ᵁ U
    let s : Γ(X, ⊤) →ₐ[ℤ] Γ(R, ⊤) := p₁.appTop.hom.toIntAlgHom
    let t : Γ(X, ⊤) →ₐ[ℤ] Γ(R, ⊤) := p₂.appTop.hom.toIntAlgHom
    let sU : Γ(X, U) →ₐ[ℤ] Γ(R, V) := (p₁.app U).hom.toIntAlgHom
    let tU : Γ(X, U) →ₐ[ℤ] Γ(R, V) :=
      (p₂.appLE U V (preimage_finrankOpen_eq h r).le).hom.toIntAlgHom
    let f : Γ(X, ⊤) →ₐ[ℤ] Γ(X, U) :=
      (X.presheaf.map (homOfLE le_top).op).hom.toIntAlgHom
    let g : Γ(R, ⊤) →ₐ[ℤ] Γ(R, V) :=
      (R.presheaf.map (homOfLE le_top).op).hom.toIntAlgHom
    let hs : g.comp s = sU.comp f := by
      ext x
      exact DFunLike.congr_fun (p₁.appTop_restriction_square U) x
    let ht : g.comp t = tU.comp f := by
      ext x
      exact DFunLike.congr_fun (p₂.appTop_restriction_square_of_eq U V
        (preimage_finrankOpen_eq h r)) x
    let φ := AlgHom.equalizerMapOfCommuting s t sU tU f g hs ht
    let _ : Algebra (AlgHom.equalizer s t) (AlgHom.equalizer sU tU) :=
      φ.toRingHom.toAlgebra
    IsLocalization.Away e (AlgHom.equalizer sU tU) := by
  dsimp only
  obtain ⟨e', he', hbasic', hloc⟩ :=
    exists_finrankOpen_equalizer_isLocalizationAway h r
  have heq : e' = e := by
    apply Subtype.ext
    apply Scheme.Opens.basicOpen_injOn_isIdempotentElem
      (he'.map (AlgHom.equalizer p₁.appTop.hom.toIntAlgHom
        p₂.appTop.hom.toIntAlgHom).val)
      (he.map (AlgHom.equalizer p₁.appTop.hom.toIntAlgHom
        p₂.appTop.hom.toIntAlgHom).val)
    exact hbasic'.trans hbasic.symm
  subst e'
  exact hloc

end AlgebraicGeometry.EquivalenceRelation
end
end
