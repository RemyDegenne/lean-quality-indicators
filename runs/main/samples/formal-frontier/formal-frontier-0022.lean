@[expose] public section

universe u v w

theorem MvPolynomial.moduleFinite_rename_iff
    {R : Type u} {σ : Type v} {τ : Type w}
    [CommSemiring R] (f : σ → τ) :
    @Module.Finite (MvPolynomial σ R) (MvPolynomial τ R)
      inferInstance inferInstance
      (@Algebra.toModule (MvPolynomial σ R) (MvPolynomial τ R)
        inferInstance inferInstance
        (MvPolynomial.rename (R := R) f).toRingHom.toAlgebra) ↔
      Function.Surjective f ∨ Subsingleton R := by
  classical
  let : Algebra (MvPolynomial σ R) (MvPolynomial τ R) :=
    (MvPolynomial.rename (R := R) f).toRingHom.toAlgebra
  change Module.Finite (MvPolynomial σ R) (MvPolynomial τ R) ↔ _
  constructor
  · intro h
    by_cases hR : Subsingleton R
    · exact Or.inr hR
    · left
      let : Nontrivial R := not_subsingleton_iff_nontrivial.mp hR
      by_contra hf
      simp only [Function.Surjective, not_forall, not_exists] at hf
      obtain ⟨j, hj⟩ := hf
      let g : τ → Polynomial R := fun t => if t = j then Polynomial.X else 0
      let e : MvPolynomial τ R →ₐ[R] Polynomial R := MvPolynomial.aeval g
      have he : Function.Surjective e := by
        intro p
        refine ⟨Polynomial.aeval (MvPolynomial.X j) p, ?_⟩
        have hsec : e.comp (Polynomial.aeval (MvPolynomial.X j)) =
            AlgHom.id R (Polynomial R) := by
          apply Polynomial.algHom_ext
          simp [e, g]
        exact DFunLike.congr_fun hsec p
      have hcomp (a : MvPolynomial σ R) :
          e (MvPolynomial.rename f a) = Polynomial.C (MvPolynomial.constantCoeff a) := by
        change MvPolynomial.eval₂Hom (algebraMap R (Polynomial R)) g
          (MvPolynomial.rename f a) = _
        rw [MvPolynomial.eval₂Hom_rename]
        have hg : g ∘ f = fun _ => 0 := by
          funext i
          exact ite_eq_right (hj i)
        rw [hg, MvPolynomial.eval₂Hom_zero'_apply]
        rfl
      let l : MvPolynomial τ R →ₛₗ[MvPolynomial.constantCoeff] Polynomial R :=
        { e.toAddMonoidHom with
          map_smul' := fun a b => by
            change e (MvPolynomial.rename f a * b) =
              MvPolynomial.constantCoeff a • e b
            rw [map_mul, hcomp]
            exact (Algebra.smul_def _ _).symm }
      let : Module.Finite (MvPolynomial σ R) (MvPolynomial τ R) := h
      exact Polynomial.not_finite (R := R) (Module.Finite.of_surjective l he)
  · rintro (hf | hR)
    · exact Module.Finite.of_surjective
        (Algebra.linearMap (MvPolynomial σ R) (MvPolynomial τ R))
        (MvPolynomial.rename_surjective f hf)
    · let := hR
      infer_instance

end
