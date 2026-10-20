namespace P2MW.S_ModularCurve_FullLevel_exists_invariant_notMem_of_endChartPole_of_rigidChart

attribute [-instance] ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 0

set_option maxHeartbeats 0

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace S3C4Glue

open IsLocalRing Polynomial

open IsLocalRing

theorem exists_eq_pow_of_stabilises {k K : Type} [Field k] [Field K] [Algebra k K]
    {R : Type} [CommRing R] [Algebra R K]
    {Γ : Type} [Group Γ] (S₀ S₁ : Subgroup Γ) (Att : Γ → (K ≃ₐ[k] K) → Prop)
    (G : Subgroup (K ≃ₐ[k] K))
    (hGatt : ∀ τ : K ≃ₐ[k] K, τ ∈ G → ∃ γ : Γ, γ ∈ S₁ ∧ γ ∈ S₀ ∧ Att γ⁻¹ τ)
    (B : Subalgebra R K) (W : ValuationSubring K)
    (hfrac : ∀ f : K, ∃ g h : ↥B, (h : K) ≠ 0 ∧ f * (h : K) = (g : K))
    (τ₀ : K ≃ₐ[k] K) (n : ℕ)
    (h72 : ∀ γ : Γ, γ ∈ S₁ → γ ∈ S₀ → ∀ τ : K ≃ₐ[k] K, Att γ⁻¹ τ → (∀ f : K, f ∈ W ↔ τ f ∈ W) →
      ∃ m : ℕ, m < n ∧ ∀ f : K, f ∈ B → τ f = (τ₀ ^ m) f)
    (O : Subring K) (hOW : ∀ f : K, f ∈ O → f ∈ W)
    (hR7oneO : ∀ γ : Γ, γ ∈ S₁ → γ ∈ S₀ → ∀ τ : K ≃ₐ[k] K, Att γ⁻¹ τ →
      (∀ f : K, f ∈ O → τ f ∈ W) → ∀ f : K, f ∈ W ↔ τ f ∈ W) :
    ∀ σ : K ≃ₐ[k] K, σ ∈ G → (∀ f : K, f ∈ O ↔ σ f ∈ O) → ∃ j : ℕ, ∀ f : K, σ f = (τ₀ ^ j) f := by
  intro σ hσ hstab
  have hob49 := hGatt σ hσ
  obtain ⟨γ, h1, h0, hatt⟩ := hob49
  have hinto : ∀ f : K, f ∈ O → σ f ∈ W := fun f hf => hOW _ ((hstab f).mp hf)
  have hW : ∀ f : K, f ∈ W ↔ σ f ∈ W := hR7oneO γ h1 h0 σ hatt hinto
  have hob50 := h72 γ h1 h0 σ hatt hW
  obtain ⟨m, -, hm⟩ := hob50
  refine ⟨m, ?_⟩
  have key := apply_eq_self_of_frac B hfrac ((τ₀ ^ m)⁻¹ * σ) (fun f hf => by
    rw [AlgEquiv.mul_apply, hm f hf, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply])
  intro f
  have h1 := key f
  rw [AlgEquiv.mul_apply] at h1
  have h2 := congrArg (τ₀ ^ m) h1
  rwa [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at h2

end S3C4Glue
end P2MW.S_ModularCurve_FullLevel_exists_invariant_notMem_of_endChartPole_of_rigidChart
