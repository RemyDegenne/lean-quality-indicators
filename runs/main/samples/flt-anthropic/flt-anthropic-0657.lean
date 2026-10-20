namespace P2MW.S_AlgebraicCurve_exists_forall_smul_div_pow_mem_integers_of_cartierData_of_balanced_of_semistableModel

attribute [-instance] AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup

set_option autoImplicit false

universe u v w

open AlgebraicCurve IsLocalRing

namespace VertAux

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem degree_eq_sum_of_isRational {K F' : Type*} [Field K] [Field F'] [Algebra K F'] (D : Divisor K F')
    (hrat : ∀ v ∈ D.support, v.IsRational) (s : Finset (Place K F')) (hs : D.support ⊆ s) :
    Divisor.degree D = ∑ v ∈ s, D v := by
  classical
  rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum]
  rw [Finset.sum_subset hs (fun v _ hv => by
    have : D v = 0 := by simpa [Finsupp.mem_support_iff] using hv
    simp [this])]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  by_cases hD : v ∈ D.support
  · simp [Place.deg_eq_one_of_isRational (hrat v hD)]
  · have : D v = 0 := by simpa [Finsupp.mem_support_iff] using hD
    simp [this]

end VertAux
end P2MW.S_AlgebraicCurve_exists_forall_smul_div_pow_mem_integers_of_cartierData_of_balanced_of_semistableModel
