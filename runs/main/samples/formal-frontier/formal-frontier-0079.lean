@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.EquivalenceRelation

universe u

variable {R X : Scheme.{u}} {p₁ p₂ : R ⟶ X}
  [Flat p₁] [IsFinite p₁] [LocallyOfFinitePresentation p₁] [IsAffine X]

lemma exists_completeOrthogonalIdempotents_equalizer_finrankOpen
    (h : CategoryTheory.EquivalenceRelation p₁ p₂) :
    let I := Set.range p₁.finrank
    let s : Γ(X, ⊤) →ₐ[ℤ] Γ(R, ⊤) := p₁.appTop.hom.toIntAlgHom
    let t : Γ(X, ⊤) →ₐ[ℤ] Γ(R, ⊤) := p₂.appTop.hom.toIntAlgHom
    ∃ e : I → AlgHom.equalizer s t,
      @CompleteOrthogonalIdempotents (AlgHom.equalizer s t) _ I
        (finrankRangeFintype (p₁ := p₁)) e ∧
        ∀ i, X.basicOpen (e i).1 = finrankOpen (p₁ := p₁) i.1 := by
  dsimp only
  let _ : Fintype (Set.range p₁.finrank) :=
    finrankRangeFintype (p₁ := p₁)
  obtain ⟨e, he, hbasic⟩ :=
    exists_completeOrthogonalIdempotents_finrankOpen h
  let s : Γ(X, ⊤) →ₐ[ℤ] Γ(R, ⊤) := p₁.appTop.hom.toIntAlgHom
  let t : Γ(X, ⊤) →ₐ[ℤ] Γ(R, ⊤) := p₂.appTop.hom.toIntAlgHom
  let eE : Set.range p₁.finrank → AlgHom.equalizer s t := fun i ↦
    ⟨e i, (hbasic i).2⟩
  have heE : CompleteOrthogonalIdempotents eE := by
    constructor
    · constructor
      · intro i
        apply Subtype.ext
        exact (he.idem i).eq
      · intro i j hij
        apply Subtype.ext
        exact he.ortho hij
    · apply Subtype.ext
      change (AlgHom.equalizer s t).val (∑ i, eE i) =
        (AlgHom.equalizer s t).val 1
      rw [map_sum, map_one]
      change ∑ i, e i = 1
      exact he.complete
  exact ⟨eE, heE, fun i ↦ (hbasic i).1⟩

end AlgebraicGeometry.EquivalenceRelation
end
end
