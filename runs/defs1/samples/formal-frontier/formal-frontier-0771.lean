public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace TopCat

namespace TopCat.Sheaf

variable {X : TopCat.{0}}

/-- The homology of three consecutive envelope terms on global sections is
the cokernel of the preceding quotient map on global sections. -/
@[expose] noncomputable def flasqueEnvelopeSectionsHomologyIsoCokernel
    (A : Sheaf AddCommGrpCat X) :
    (flasqueEnvelopeSectionsShortComplex A).homology ≅
      cokernel (((toFlasqueEnvelopeQuotient (X := X)).app A).hom.app
        (op (⊤ : Opens X))) := by
  let B := (flasqueEnvelopeQuotientFunctor (X := X)).obj A
  let C := (flasqueEnvelopeQuotientFunctor (X := X)).obj B
  let S := flasqueEnvelopeSectionsShortComplex A
  let p : S.X₁ ⟶ B.obj.obj (op (⊤ : Opens X)) :=
    ((toFlasqueEnvelopeQuotient (X := X)).app A).hom.app
      (op (⊤ : Opens X))
  let i : B.obj.obj (op (⊤ : Opens X)) ⟶ S.X₂ :=
    ((toFlasqueEnvelope (X := X)).app B).hom.app
      (op (⊤ : Opens X))
  have hfi : p ≫ i = S.f := by
    rfl
  have hig : i ≫ S.g = 0 := by
    have h := congr_app
      (toFlasqueEnvelope_comp_toFlasqueEnvelopeQuotient (X := X)) B
    change
      (toFlasqueEnvelope (X := X)).app B ≫
        (toFlasqueEnvelopeQuotient (X := X)).app B = 0 at h
    have hs :
        (toFlasqueEnvelope (X := X)).app B ≫
          ((toFlasqueEnvelopeQuotient (X := X)).app B ≫
            (toFlasqueEnvelope (X := X)).app C) = 0 := by
      rw [← Category.assoc, h, zero_comp]
    exact congrArg (fun k ↦ k.hom.app (op (⊤ : Opens X))) hs
  have hi : IsLimit (KernelFork.ofι i hig) := by
    let core : ShortComplex AddCommGrpCat :=
      { f := ((toFlasqueEnvelope (X := X)).app B).hom.app
          (op (⊤ : Opens X))
        g := ((toFlasqueEnvelopeQuotient (X := X)).app B).hom.app
          (op (⊤ : Opens X))
        zero := congrArg (fun k ↦ k.hom.app (op (⊤ : Opens X)))
          (congr_app
            (toFlasqueEnvelope_comp_toFlasqueEnvelopeQuotient (X := X)) B) }
    have hcore : core.Exact := by
      rw [ShortComplex.ab_exact_iff]
      intro x hx
      exact Sheaf.sections_exact_of_left_exact
        (flasqueEnvelopeShortExact B).exact
        (flasqueEnvelopeShortExact B).mono_f x hx
    let target : ShortComplex AddCommGrpCat := ShortComplex.mk i S.g hig
    let a : core ⟶ target :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := ((toFlasqueEnvelope (X := X)).app C).hom.app
          (op (⊤ : Opens X))
        comm₁₂ := by rfl
        comm₂₃ := by rfl }
    let _ : Epi a.τ₁ := by dsimp [a]; infer_instance
    let _ : IsIso a.τ₂ := by dsimp [a]; infer_instance
    let _ : Mono a.τ₃ := by dsimp [a]; infer_instance
    have htarget : target.Exact :=
      (ShortComplex.exact_iff_of_epi_of_isIso_of_mono a).1 hcore
    exact htarget.fIsKernel
  exact ShortComplex.homologyIsoCokernelOfKernelFactorization
    S (B.obj.obj (op (⊤ : Opens X))) p i hfi hig hi

end TopCat.Sheaf
end
end
