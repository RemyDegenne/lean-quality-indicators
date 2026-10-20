namespace P2MW.S_ModularCurve_MultCovering_hasseExp_le_two_of_thirteen_le

attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.GaussReduction.isLocalHom_constToGauss ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure

set_option autoImplicit false

set_option maxHeartbeats 3200000

set_option synthInstance.maxHeartbeats 3200000

set_option Elab.async false

p2m_open

namespace ModularCurve

namespace MultCovering

p2m_open

variable {p : ℕ} [Fact p.Prime] {r : ℕ}

section Bound

open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.LevelOneProlongationPair

variable (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)

include hA in

theorem annOut_wide (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμp : μ (p : AlgebraicClosure ℚ) < 1)
    (e : Fin (mAnnuli p)) :
    ∃ Q₁ ∈ (Δ.annOut e).dom, ∃ Q₂ ∈ (Δ.annOut e).dom,
      μ (Q₁.evalAt (Δ.annOut e).param) ≠ μ (Q₂.evalAt (Δ.annOut e).param) := by
  obtain ⟨c₁, hc₁, -, Q₁, hQ₁, hQ₁c⟩ := exists_mem_dom_evalAt_eq_root p A hA Γ Δ e 2 le_rfl
  obtain ⟨c₂, hc₂, -, Q₂, hQ₂, hQ₂c⟩ := exists_mem_dom_evalAt_eq_root p A hA Γ Δ e 4 (by norm_num)
  refine ⟨Q₁, hQ₁, Q₂, hQ₂, ?_⟩
  rw [hQ₁c, hQ₂c]
  intro h
  have hμp0 : 0 < μ (p : AlgebraicClosure ℚ) := μ.pos (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have h1 : μ c₁ ^ 4 = μ (p : AlgebraicClosure ℚ) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ← map_pow, hc₁]
  have h2 : μ c₂ ^ 4 = μ (p : AlgebraicClosure ℚ) := by rw [← map_pow, hc₂]
  rw [h] at h1
  rw [h1] at h2

  nlinarith

end Bound
end MultCovering
end ModularCurve
end P2MW.S_ModularCurve_MultCovering_hasseExp_le_two_of_thirteen_le
