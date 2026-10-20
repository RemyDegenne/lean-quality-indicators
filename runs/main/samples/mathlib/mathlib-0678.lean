@[expose] public section

open MeasureTheory Set Filter

open scoped NNReal Topology

namespace CFC

open Real

section NonUnitalCFC

variable {A : Type*} [NonUnitalNormedRing A] [StarRing A] [NormedSpace ℝ A] [SMulCommClass ℝ A A]
  [IsScalarTower ℝ A A] [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
  [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

variable (A) in
lemma exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁ [CompleteSpace A] {p : ℝ≥0}
    (hp : p ∈ Ioo 0 1) :
    ∃ μ : Measure ℝ, ∀ a ∈ Ici (0 : A),
      (IntegrableOn (fun t => cfcₙ (rpowIntegrand₀₁ p t) a) (Ioi 0) μ)
      ∧ a ^ p = ∫ t in Ioi 0, cfcₙ (rpowIntegrand₀₁ p t) a ∂μ := by
  obtain ⟨μ, hμ⟩ := exists_measure_rpow_eq_integral_rpowIntegrand₀₁ hp
  refine ⟨μ, fun a (ha : 0 ≤ a) => ?_⟩
  nontriviality A
  have p_pos : 0 < (p : ℝ) := by exact_mod_cast hp.1
  let f t := rpowIntegrand₀₁ p t
  let maxr := sSup (quasispectrum ℝ a)
  have maxr_nonneg : 0 ≤ maxr :=
    le_csSup_of_le (b := 0) (IsCompact.bddAbove (by grind)) (by simp) (by simp)
  let bound (t : ℝ) := ‖f t maxr‖
  have hf : ContinuousOn (Function.uncurry f) (Ioi (0 : ℝ) ×ˢ quasispectrum ℝ a) := by
    refine continuousOn_rpowIntegrand₀₁_uncurry hp (quasispectrum ℝ a) ?_
    grind
  have hbound : ∀ᵐ t ∂μ.restrict (Ioi 0), ∀ z ∈ quasispectrum ℝ a, ‖f t z‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro z hz
    have hz' : 0 ≤ z := by grind
    unfold bound f
    rw [Real.norm_of_nonneg (rpowIntegrand₀₁_nonneg p_pos (le_of_lt ht) hz'),
        Real.norm_of_nonneg (rpowIntegrand₀₁_nonneg p_pos (le_of_lt ht) maxr_nonneg)]
    refine rpowIntegrand₀₁_monotoneOn hp (le_of_lt ht) hz' maxr_nonneg ?_
    exact le_csSup (IsCompact.bddAbove (quasispectrum.isCompact _)) hz
  have hbound_finite_integral : HasFiniteIntegral bound (μ.restrict (Ioi 0)) := by
    rw [hasFiniteIntegral_norm_iff]
    exact (hμ maxr maxr_nonneg).1.2
  have hmapzero : ∀ᵐ (x : ℝ) ∂μ.restrict (Ioi 0), rpowIntegrand₀₁ p x 0 = 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi]
    simp
  refine ⟨?integrable, ?integral⟩
  case integrable =>
    exact integrableOn_cfcₙ measurableSet_Ioi _ bound a hf hmapzero hbound hbound_finite_integral
  case integral => calc
    a ^ p = cfcₙ (fun r => ∫ t in Ioi 0, rpowIntegrand₀₁ p t r ∂μ) a := by
      rw [nnrpow_eq_cfcₙ_real _ _]
      exact cfcₙ_congr fun r _ ↦ (hμ r (by grind)).2
    _ = _ := cfcₙ_setIntegral measurableSet_Ioi _ bound a hf hmapzero hbound
                hbound_finite_integral ha.isSelfAdjoint

end NonUnitalCFC
end CFC
end
