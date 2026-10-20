namespace P2MW.S_exists_residualRep_descent

set_option autoImplicit false

open T10DescSol in
set_option maxHeartbeats 3200000 in
theorem solution {k : Type} [Field k] (ρbar : ResidualGaloisRep k)
    (L₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L₀]
    [NumberField L₀] [IsGalois ℚ L₀]
    (hker : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      (∀ x ∈ L₀, σ x = x) → ρbar.ρ σ = 1)
    (b : Module.Basis (Fin 2) k ρbar.V) :
    ∃ ρmat : TaylorWiles.ResidualRep (↥L₀) k,
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        ρmat (AlgEquiv.restrictNormalHom (↥L₀) σ)
          = LinearMap.toMatrix b b (ρbar.ρ σ) := by
  classical
  haveI hnorm : Normal ℚ (↥L₀) := IsGalois.to_normal
  have hker_le : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) (↥L₀)).ker
      ≤ (matAux ρbar b).toHomUnits.ker := by
    intro σ hσ
    rw [MonoidHom.mem_ker] at hσ ⊢
    have h1 : ∀ x ∈ L₀, σ x = x := by
      intro x hx
      have h2 := @AlgEquiv.restrictNormalHom_apply ℚ _ (AlgebraicClosure ℚ) _ _ L₀ hnorm σ ⟨x, hx⟩
      have h4 := congrArg Subtype.val (AlgEquiv.ext_iff.mp hσ ⟨x, hx⟩)
      exact h2.symm.trans h4
    refine Units.ext ?_
    show LinearMap.toMatrix b b (ρbar.ρ σ) = 1
    rw [hker σ h1]
    exact LinearMap.toMatrix_id b
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI hnormQbar : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  have hsurj : Function.Surjective
      (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) (↥L₀)) :=
    AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure ℚ)
  refine ⟨(Units.coeHom (Matrix (Fin 2) (Fin 2) k)).comp (liftAuxU ρbar L₀ b hsurj hker_le),
    fun σ => ?_⟩
  show (↑(liftAuxU ρbar L₀ b hsurj hker_le (AlgEquiv.restrictNormalHom (↥L₀) σ)) :
      Matrix (Fin 2) (Fin 2) k) = LinearMap.toMatrix b b (ρbar.ρ σ)
  exact congrArg Units.val (liftAuxU_spec ρbar L₀ b hsurj hker_le σ)

end P2MW.S_exists_residualRep_descent
