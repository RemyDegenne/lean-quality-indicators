@[expose] public section

universe u v w

namespace MvPolynomial

variable {R : Type u} {σ : Type v} {τ : Type w} [CommRing R]

@[simp]
theorem isAlgebraic_X_rename_iff (f : σ → τ) (j : τ) :
    @IsAlgebraic (MvPolynomial σ R) (MvPolynomial τ R)
      inferInstance inferInstance
      (rename (R := R) f).toRingHom.toAlgebra (X j) ↔
        Nontrivial R ∧ (j ∈ Set.range f ∨ ¬ Function.Injective f) := by
  classical
  let : Algebra (MvPolynomial σ R) (MvPolynomial τ R) :=
    (rename (R := R) f).toRingHom.toAlgebra
  constructor
  · intro h
    have : Nontrivial (MvPolynomial σ R) := h.nontrivial
    have hR : Nontrivial R := (C : R →+* MvPolynomial σ R).domain_nontrivial
    refine ⟨hR, ?_⟩
    by_cases hf : Function.Injective f
    · left
      by_contra hj
      let g : MvPolynomial σ R →ₐ[R] supported R (Set.range f) :=
        (rename (R := R) f).codRestrict (supported R (Set.range f)) (fun p => by
          rw [mem_supported]
          intro j hj
          obtain ⟨i, _, rfl⟩ := mem_vars_rename f p hj
          exact ⟨i, rfl⟩)
      have hg : Function.Injective g := by
        intro p q hpq
        apply rename_injective f hf
        exact congrArg Subtype.val hpq
      have hcomp :
          (algebraMap (supported R (Set.range f)) (MvPolynomial τ R)).comp g.toRingHom =
            (RingHom.id (MvPolynomial τ R)).comp
              (algebraMap (MvPolynomial σ R) (MvPolynomial τ R)) := by
        ext p <;> rfl
      have hx := h.ringHom_of_comp_eq
        g.toRingHom (RingHom.id (MvPolynomial τ R)) hg hcomp
      exact (transcendental_supported_X R (show j ∉ Set.range f from hj)) hx
    · exact Or.inr hf
  · rintro ⟨hR, hj | hf⟩
    · have : Nontrivial R := hR
      obtain ⟨i, rfl⟩ := hj
      have hx : IsAlgebraic (MvPolynomial σ R)
          ((rename (R := R) f) (X i)) := isAlgebraic_algebraMap (X i)
      simpa only [rename_X] using hx
    · have : Nontrivial R := hR
      have : Algebra.IsAlgebraic (MvPolynomial σ R) (MvPolynomial τ R) := by
        apply Algebra.isAlgebraic_of_not_injective
        intro hi
        rcases (injective_rename_iff f).1 hi with hfi | hsub
        · exact hf hfi
        · exact zero_ne_one (hsub.elim 0 1)
      exact Algebra.IsAlgebraic.isAlgebraic (R := MvPolynomial σ R) (X j)

end MvPolynomial
end
