namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_Extension_relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

set_option maxSynthPendingDepth 3

open NumberField IsDedekindDomain

open scoped TensorProduct

noncomputable section

namespace P2mLocalIndex

attribute [-instance] IsLocalRing.ResidueField.algebraOfIsIntegral IsLocalRing.ResidueField.isScalarTowerOfIsIntegral

theorem main
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (hprime : (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)).Prime)
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hθ : orderOf θ = Module.finrank (v.adicCompletion K) (w.1.adicCompletion L))
    (hres : ∃ y : w.1.adicCompletion L, ‖y‖ ≤ 1 ∧ ‖θ y - y‖ = 1)
    (c : w.1.adicCompletion L) (n : v.adicCompletion K) (hn : ‖n‖ = 1) (m : ℕ)
    (hm : ‖1 - n‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(m : ℤ)))
    (hc : ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)), (θ ^ i) c =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) n)
    (ϖ : v.adicCompletion K) (hϖ : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹) (s : ℕ) :
    (w.1.adicCompletionIntegers L).toAddSubgroup.relIndex
        (((w.1.adicCompletionIntegers L).toAddSubgroup.comap
            (θ.toAlgHom.toRingHom.toAddMonoidHom - AddMonoidHom.mulLeft c)) ⊓
          ((w.1.adicCompletionIntegers L).toAddSubgroup.comap
            (AddMonoidHom.mulLeft
              (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (ϖ ^ s))))) =
      Ideal.absNorm v.asIdeal ^ min s m := by
  have hn1 : (Valued.v n : WithZero (Multiplicative ℤ)) = 1 := v_eq_one_of_norm_eq_one K v hn
  have hcunit := v_c_eq_one K L v w θ hw hprime.pos c n hn1 hc
  have hcO : c ∈ w.1.adicCompletionIntegers L := (mem_integers_iff_v L w.1 c).2 hcunit.le
  haveI := finite_residueField K v
  have hI := LinearMap.relIndex_pow_smul_top_comap_eq_card_pow_min_of_finrank_ker_baseChange_le_one
    (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) (fO K L v w θ c hcO)
    (fO_injective K L v w θ c hcO hθ n hc m hm)
    (finrank_ker_le_one K L v w θ c hcO hθ hw ϖ hϖ hres hprime hcunit)
    (piO K v ϖ hϖ) (irreducible_piO K v ϖ hϖ) m
    (associated_det_fO K L v w θ c hcO hθ n hc m hm ϖ hϖ) s
  rw [card_residueField] at hI
  rw [← hI, ← AddSubgroup.relIndex_map_map_of_injective _ _ (iota_injective K L v w),
    map_iota_smul_top K L v w ϖ hϖ s, map_iota_comap K L v w θ c hcO ϖ hϖ s,
    AddSubgroup.relIndex_map_map_of_injective _ _ (mulLeft_pis_injective K L v w ϖ hϖ s)]

end P2mLocalIndex
end
end P2MW.S_IsDedekindDomain_HeightOneSpectrum_Extension_relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one
