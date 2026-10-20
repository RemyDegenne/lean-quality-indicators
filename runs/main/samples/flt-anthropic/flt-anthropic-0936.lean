namespace P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators

attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

set_option autoImplicit false

universe u

p2m_open

open scoped TensorProduct

p2m_reactivate

set_option synthInstance.maxHeartbeats 400000

set_option Elab.async false

noncomputable section

p2m_open

open scoped TensorProduct

p2m_reactivate

set_option maxHeartbeats 800000

set_option synthInstance.maxHeartbeats 400000

set_option Elab.async false

p2m_open

open scoped TensorProduct

p2m_reactivate

p2m_open_scoped

noncomputable section

namespace TensorAdapt

open AlgebraicCurve AlgebraicCurve.CurveModel

p2m_reactivate

p2m_reactivate

p2m_reactivate

section MidLift

open AlgebraicCurve.TwoChartIntegralModel

variable (p : ℕ) [Fact p.Prime] {F : Type} [Field F] (j : F) [Fact (j ≠ 0)]
  (𝔭 : Ideal ↥(chartAlgFin ℤ F j)) (e : (↥(chartAlgFin ℤ F j) ⧸ 𝔭) ≃+* (ZMod p)[X]) (m : ℕ)

variable (hej : e (Ideal.Quotient.mk 𝔭 (jChartFin ℤ F j)) = Polynomial.X ^ m)

theorem ρ₀'_inclAdj_mem (x : F) (hx : x ∈ Algebra.adjoin ℤ ({j⁻¹} : Set F)) :
    ρ₀' p j 𝔭 e m hej (inclAdj j ⟨x, hx⟩) ∈ Algebra.adjoin (ZMod p) ({(RatFunc.X : RatFunc (ZMod p))⁻¹} : Set (RatFunc (ZMod p))) := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      have : inclAdj j ⟨j⁻¹, Algebra.subset_adjoin (Set.mem_singleton _)⟩ = jInvChartInf ℤ F j := Subtype.ext rfl
      rw [this, ρ₀'_jInv p j 𝔭 e m hej (Or.inr trivial), ← inv_pow]
      exact pow_mem (Algebra.subset_adjoin (Set.mem_singleton _)) m
  | algebraMap r =>
      have : inclAdj j ⟨algebraMap ℤ F r, Subalgebra.algebraMap_mem _ r⟩ = algebraMap ℤ _ r := Subtype.ext rfl
      rw [this, ← RingHom.comp_apply, eq_intCast]
      exact intCast_mem _ r
  | add x y hx hy ihx ihy =>
      have : inclAdj j ⟨x + y, add_mem hx hy⟩ = inclAdj j ⟨x, hx⟩ + inclAdj j ⟨y, hy⟩ := Subtype.ext rfl
      rw [this, map_add]; exact add_mem ihx ihy
  | mul x y hx hy ihx ihy =>
      have : inclAdj j ⟨x * y, mul_mem hx hy⟩ = inclAdj j ⟨x, hx⟩ * inclAdj j ⟨y, hy⟩ := Subtype.ext rfl
      rw [this, map_mul]; exact mul_mem ihx ihy

end MidLift
end TensorAdapt
end
end
end P2MW.S_ModularCurve_DRModel_exists_curveModel_ratFunc_closedImmersion_pair_pFibre_and_range_sectionFibre_subset_of_residue_generators
