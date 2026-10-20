namespace P2MW.S_ModularCurve_FullLevel_klevel_smoothPointStalks_of_baseSmoothPointStalks_linked

attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.GaussReduction.isLocalHom_constToGauss

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 1600000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup

open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 6400000

namespace KLevelGeomReduce

theorem LayerDVR_stub {k₀ L : Type} [Field k₀] [Field L] [Algebra k₀ L] (A : ValuationSubring L)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap k₀ L)))
    (K : IntermediateField k₀ L) (hK : FiniteDimensional k₀ ↥K)
    (AK : ValuationSubring ↥K) (hAK : ∀ x : ↥K, x ∈ AK ↔ (x : L) ∈ A) :
    IsDiscreteValuationRing ↥AK ∧ ∃ ϖ : ↥AK, maximalIdeal ↥AK = Ideal.span {ϖ} ∧ ϖ ≠ 0 := by
  suffices hd : IsDiscreteValuationRing ↥AK by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥AK
    exact ⟨hd, ϖ, hϖ.maximalIdeal_eq, hϖ.ne_zero⟩
  haveI := hdvr
  haveI := hK
  letI : Algebra ↥(A.comap (algebraMap k₀ L)) ↥K :=
    ((algebraMap k₀ ↥K).comp (algebraMap ↥(A.comap (algebraMap k₀ L)) k₀)).toAlgebra
  haveI : IsScalarTower ↥(A.comap (algebraMap k₀ L)) k₀ ↥K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  refine ValuationSubring.isDiscreteValuationRing_of_algebraMap_mem_of_finite
    (A := ↥(A.comap (algebraMap k₀ L))) (K := k₀) AK ?_ ?_
  · intro a
    rw [hAK]
    have ha : algebraMap k₀ L (a : k₀) ∈ A := ValuationSubring.mem_comap.mp a.2
    have : ((algebraMap k₀ ↥K (a : k₀) : ↥K) : L) = algebraMap k₀ L (a : k₀) :=
      (IsScalarTower.algebraMap_apply k₀ ↥K L (a : k₀)).symm
    show ((algebraMap k₀ ↥K (a : k₀) : ↥K) : L) ∈ A
    rw [this]; exact ha
  · intro htop
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(A.comap (algebraMap k₀ L))
    have hϖ0 : (ϖ : k₀) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
    have hinvK : algebraMap k₀ ↥K ((ϖ : k₀)⁻¹) ∈ AK := by rw [htop]; exact ValuationSubring.mem_top _
    have hinv : algebraMap k₀ L ((ϖ : k₀)⁻¹) ∈ A := by
      rw [hAK, IntermediateField.coe_algebraMap_apply] at hinvK
      exact hinvK
    have hmem : (ϖ : k₀)⁻¹ ∈ A.comap (algebraMap k₀ L) := ValuationSubring.mem_comap.mpr hinv
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one ⟨_, hmem⟩ (Subtype.ext (mul_inv_cancel₀ hϖ0)))

end KLevelGeomReduce
end P2MW.S_ModularCurve_FullLevel_klevel_smoothPointStalks_of_baseSmoothPointStalks_linked
