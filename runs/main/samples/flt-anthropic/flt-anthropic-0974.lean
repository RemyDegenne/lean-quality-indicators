namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_eq_of_represents_of_represents_of_constantCoeff_eq_zero

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField

open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem solution
    {r N : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (coord : ↥Λ → Zp2 r × Zp2 r)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2)
    (B : Type) [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B)
    (E : FakeEllipticCurve Λ N B) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E)
    (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (hX : E.IsFormalModuleVia coord X θ)
    (σ₁ σ₂ : Series (B ⧸ Ideal.span {algebraMap 𝒪 B π}))
    (h0₁ : ∀ i, MvPowerSeries.constantCoeff (σ₁ i) = 0) (h0₂ : ∀ i, MvPowerSeries.constantCoeff (σ₂ i) = 0)
    (h₁ : (∀ (B'' : Type) [CommRing B''] [Algebra (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B''] [Algebra B B'']
        [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
        algebraMap B B'' = (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (Ideal.Quotient.mk _) →
        algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' = (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) →
        ∀ (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          ∀ PA : Spec (CommRingCat.of B'') ⟶ ρ.Ab.A,
            PA ≫ ρ.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'')) →
            PA ≫ ρ.gA = (θ₀ B'' s).1 →
              PA ≫ ρ.φ' ≫ ρ.gb = (θ B'' (fun i => MvFormalGroup.nilEval m (σ₁ i) s)).1))
    (h₂ : (∀ (B'' : Type) [CommRing B''] [Algebra (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B''] [Algebra B B'']
        [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
        algebraMap B B'' = (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (Ideal.Quotient.mk _) →
        algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' = (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) →
        ∀ (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          ∀ PA : Spec (CommRingCat.of B'') ⟶ ρ.Ab.A,
            PA ≫ ρ.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'')) →
            PA ≫ ρ.gA = (θ₀ B'' s).1 →
              PA ≫ ρ.φ' ≫ ρ.gb = (θ B'' (fun i => MvFormalGroup.nilEval m (σ₂ i) s)).1)) :
    σ₁ = σ₂ := by
  classical
  funext i
  apply RUu4_eq_of_forall_nilEval_eq
  intro C _ _ J m hJ s hs

  letI iB : Algebra B C :=
    ((algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) C).comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))).toAlgebra
  letI iK : Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) C :=
    ((algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) C).comp (FakeEllipticCurve.Rigidification.residueLeg π ψ)).toAlgebra
  have hc1 : algebraMap B C =
      (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) C).comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) := rfl
  have hc2 : algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) C =
      (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) C).comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) := rfl

  obtain ⟨hsq, -, -, -⟩ := ρ.isPullback_Ab
  have w : (θ₀ C s).1 ≫ A₀.f =
      Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) C)) ≫
        Spec.map (CommRingCat.ofHom (FakeEllipticCurve.Rigidification.residueLeg π ψ)) := by
    rw [(θ₀ C s).2, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hc2]
  set PA : Spec (CommRingCat.of C) ⟶ ρ.Ab.A := hsq.lift (θ₀ C s).1
    (Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) C))) w with hPA
  have hPAg : PA ≫ ρ.gA = (θ₀ C s).1 := hsq.lift_fst _ _ w
  have hPAf : PA ≫ ρ.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) C)) :=
    hsq.lift_snd _ _ w
  have e₁ := h₁ C hc1 hc2 J m hJ s hs PA hPAf hPAg
  have e₂ := h₂ C hc1 hc2 J m hJ s hs PA hPAf hPAg

  have hθinj := (hX.1.2 C J m hJ).2.1
    (fun i => MvFormalGroup.nilEval m (σ₁ i) s) (fun i => MvFormalGroup.nilEval m (σ₂ i) s)
    (fun i => RUu4_nilEval_mem C J m _ (h0₁ i) s hs) (fun i => RUu4_nilEval_mem C J m _ (h0₂ i) s hs)
    (Subtype.ext (e₁.symm.trans e₂))
  exact congrFun hθinj i

end P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_eq_of_represents_of_represents_of_constantCoeff_eq_zero
