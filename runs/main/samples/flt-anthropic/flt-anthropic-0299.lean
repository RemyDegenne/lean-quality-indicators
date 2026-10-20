namespace P2MW.S_ModularCurve_FullLevel_supersingularProlongation_smoothPointPackage_disc_subset_of_eq_three_of_dvd

attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt

set_option autoImplicit false

p2m_open

open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace AlgebraicCurve

namespace DiscRigidity

p2m_open

attribute [local instance] Classical.propDecidable

variable {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]

variable (A : ValuationSubring L) {Fbar : Type*} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]

theorem sum_filter_eq_of_degreeOn (R : RegularProlongation A F Fbar) (Q : Place (ResidueField ↥A) Fbar)
    (D D' : Set (Place L F)) (hD : R.DegreeOn Q D) (hD' : R.DegreeOn Q D')
    (f : F) (hf : f ≠ 0) (Df : Divisor L F) (hDf : ∀ v, Df v = v.ord f) :
    (∑ v ∈ Df.support with v ∈ D, Df v) = ∑ v ∈ Df.support with v ∈ D', Df v := by
  classical
  obtain ⟨c, hcf, hres⟩ := R.exists_smul_mem f hf
  have hc : c ≠ 0 := by
    rintro rfl
    apply hres
    have : (⟨(0 : L) • f, hcf⟩ : R.integers) = 0 := Subtype.ext (by simp)
    rw [this, map_zero]
  have hord : ∀ v : Place L F, v.ord (c • f) = v.ord f := fun v => by
    rw [Algebra.smul_def]; exact ord_algebraMap_mul v hc hf
  have key : ∀ X : Set (Place L F), R.DegreeOn Q X →
      (Df.filter (· ∈ X)).sum (fun _ n => n) = Q.ord (R.residue ⟨c • f, hcf⟩) := fun X hX =>
    hX ⟨c • f, hcf⟩ hres (Df.filter (· ∈ X))
      (fun P hP => by rw [Finsupp.filter_apply_pos _ _ hP, hDf, hord])
      (fun P hP => by rw [Finsupp.filter_apply_neg _ _ hP])
  have e : ∀ X : Set (Place L F), (Df.filter (· ∈ X)).sum (fun _ n => n) = ∑ v ∈ Df.support with v ∈ X, Df v := by
    intro X
    rw [Finsupp.sum, Finsupp.support_filter]
    apply Finset.sum_congr rfl
    intro v hv
    rw [Finset.mem_filter] at hv
    rw [Finsupp.filter_apply_pos _ _ hv.2]
  rw [← e D, ← e D', key D hD, key D' hD']

end DiscRigidity
end AlgebraicCurve
end P2MW.S_ModularCurve_FullLevel_supersingularProlongation_smoothPointPackage_disc_subset_of_eq_three_of_dvd
