@[expose] public section

namespace MvPolynomial

universe u v w

theorem rename_smooth_iff {R : Type u} [CommRing R] {σ : Type v} {τ : Type w}
    (f : σ → τ) :
    (MvPolynomial.rename (R := R) f).toRingHom.Smooth ↔
      (Function.Injective f ∧ Set.Finite ((Set.range f)ᶜ)) ∨ Subsingleton R := by
  classical
  constructor
  · intro h
    rcases (rename_flat_iff (R := R) f).mp h.flat with hf | hR
    · have hft := RingHom.FiniteType.of_finitePresentation h.finitePresentation
      rcases (finiteType_rename_iff (R := R) f).mp hft with hR | hfinite
      · exact Or.inr hR
      · exact Or.inl ⟨hf, hfinite⟩
    · exact Or.inr hR
  · rintro (⟨hf, hfinite⟩ | hR)
    · letI : Fintype ((Set.range f)ᶜ : Set τ) := hfinite.fintype
      let e₁ := renameEquiv R (Equiv.ofInjective f hf)
      let e₂ := splitComplAlgEquiv (R := R) (Set.range f)
      have hrename :
          (rename (R := R) (Subtype.val : Set.range f → τ)).comp e₁.toAlgHom =
            rename (R := R) f := by
        apply algHom_ext
        intro i
        simp [e₁, renameEquiv_apply]
      have hcomp : e₂.symm.toRingEquiv.toRingHom.comp
          ((C : MvPolynomial (Set.range f) R →+*
            MvPolynomial ((Set.range f)ᶜ : Set τ) (MvPolynomial (Set.range f) R)).comp
            e₁.toRingEquiv.toRingHom) = (rename (R := R) f).toRingHom := by
        apply RingHom.ext
        intro p
        apply e₂.injective
        change e₂ (e₂.symm (C (e₁ p))) = e₂ (rename f p)
        have hr : rename f p = rename (Subtype.val : Set.range f → τ) (e₁ p) :=
          (DFunLike.congr_fun hrename p).symm
        rw [AlgEquiv.apply_symm_apply, hr]
        exact (splitComplAlgEquiv_rename_subtypeVal (R := R) (Set.range f) (e₁ p)).symm
      have hC : (C : MvPolynomial (Set.range f) R →+*
          MvPolynomial ((Set.range f)ᶜ : Set τ) (MvPolynomial (Set.range f) R)).Smooth := by
        change (algebraMap (MvPolynomial (Set.range f) R)
          (MvPolynomial ((Set.range f)ᶜ : Set τ) (MvPolynomial (Set.range f) R))).Smooth
        exact RingHom.smooth_algebraMap.mpr
          (show Algebra.Smooth (MvPolynomial (Set.range f) R)
            (MvPolynomial ((Set.range f)ᶜ : Set τ) (MvPolynomial (Set.range f) R)) from
              ⟨inferInstance, inferInstance⟩)
      have h₁ : e₁.toRingEquiv.toRingHom.Smooth :=
        RingHom.Smooth.of_bijective e₁.bijective
      rw [← hcomp]
      exact (h₁.comp hC).comp (RingHom.Smooth.of_bijective e₂.symm.bijective)
    · letI : Subsingleton R := hR
      exact RingHom.Smooth.of_bijective
        (Function.bijective_of_subsingleton' ((rename (R := R) f).toRingHom))

end MvPolynomial
end
