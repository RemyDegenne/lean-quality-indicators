namespace P2MW.S_AlgebraicCurve_NodeAnnulusEngine_toNat_ord_eq_length_localizedModule_of_forall_iff_evalAt_eq_zero

attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instTopologicallyFGOfFiniteType

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.UVCrossingModel

open scoped IntermediateField

namespace R1AF8D2b

section Completion

variable {A : Type*} [CommRing A] [IsNoetherianRing A] (I : Ideal A)

theorem exists_sub_of_mem_map (x : AdicCompletion I A) :
    ∃ a : A, x - AdicCompletion.of I A a ∈ I.map (algebraMap A (AdicCompletion I A)) := by
  classical
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective I A x
  refine ⟨a 1, ?_⟩
  set y := AdicCompletion.mk I A a - AdicCompletion.of I A (a 1) with hy

  have hval : ∀ n, y.val n = Submodule.Quotient.mk (a n - a 1) := fun n => rfl
  have hker : AdicCompletion.map I (Submodule.mkQ (I : Submodule A A)) y = 0 := by
    ext n
    rw [AdicCompletion.map_val_apply, hval, LinearMap.reduceModIdeal_apply, AdicCompletion.val_zero_apply]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · apply (Submodule.Quotient.mk_eq_zero _).mpr
      rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      trivial
    · have h1 : a n - a 1 ∈ I := by
        have := (AdicCompletion.AdicCauchySequence.mk_eq_mk (I := I) hn a)
        rw [Submodule.Quotient.eq] at this
        simpa [pow_one] using this
      have : Submodule.mkQ (I : Submodule A A) (a n - a 1) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact h1
      rw [this, Submodule.Quotient.mk_zero]

  have hex := AdicCompletion.map_exact (I := I) (Submodule.injective_subtype (I : Submodule A A))
    (LinearMap.exact_subtype_mkQ (I : Submodule A A)) (Submodule.mkQ_surjective _)
  obtain ⟨z, hz⟩ := (hex y).mp hker

  obtain ⟨w, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I (↥(I : Submodule A A)) z
  rw [← hz]
  clear hz
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact Ideal.zero_mem _
  | tmul r i =>
    rw [AdicCompletion.ofTensorProduct_tmul, map_smul, AdicCompletion.map_of, Submodule.subtype_apply]
    have : r • AdicCompletion.of I A (i : A) = r * algebraMap A (AdicCompletion I A) (i : A) := rfl
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ i.2)
  | add w₁ w₂ h₁ h₂ =>
    rw [map_add, map_add]
    exact Ideal.add_mem _ h₁ h₂

end Completion
end R1AF8D2b
end
end P2MW.S_AlgebraicCurve_NodeAnnulusEngine_toNat_ord_eq_length_localizedModule_of_forall_iff_evalAt_eq_zero
