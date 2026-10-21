namespace OAI

section

open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical

open scoped Topology NNReal ENNReal

namespace SLEExactGauge

noncomputable section

lemma window_source_mgf_pos_at_starts {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {ℱ : Filtration ℝ≥0 mΩ}
    {D : Set ℂ} {r R K : ℝ} {γ : ℝ≥0 → Ω → ℂ}
    {σ τ : ℂ → Ω → WithTop ℝ≥0} {Y μ : ℂ → Ω → ℝ}
    (h : SourceDisjointWindows P ℱ D r R K γ σ τ Y μ)
    {θ : ℝ} (hθ : 0 ≤ θ) {W : Ω → ℝ} (hWa : Measurable[mΩ] W) (hWs : ∀ z, Measurable[(h.start z).measurableSpace] W)
    (hW0 : ∀ ω, 0 ≤ W ω) (hWb : ∃ M, ∀ ω, W ω ≤ M) (hK : 0 < K) :
    (∫ ω, W ω * Real.exp (θ*∫ z in D, (Y z ω-μ z ω)) ∂P) ≤
      (∫ ω, W ω ∂P) * Real.exp (128*K^2*θ^2*R^2) := by
  obtain ⟨n,a,ha,han,hsep,haR⟩ := window_choose_grid (h.radius_pos.trans_le h.radius_le) h.radius_small
  let : LinearOrder (Fin n × Fin n) := LinearOrder.lift' toLex toLex.injective
  let F (ξ : ℝ × ℝ) (ω : Ω) := a^2 * ∑ i : Fin n × Fin n,
    (Y (windowCenter a ξ i) ω - μ (windowCenter a ξ i) ω)
  have hcenter (i : Fin n × Fin n) : Measurable (fun ξ => windowCenter a ξ i) :=
    Complex.measurableEquivRealProd.symm.measurable.comp
      (((measurable_fst.add_const _).sub_const _).prodMk ((measurable_snd.add_const _).sub_const _))
  have hmeas : Measurable (Function.uncurry F) := by
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i hi
    exact (h.joint_output.sub h.joint_mean).comp
      (((hcenter i).comp measurable_fst).prodMk measurable_snd)
  obtain ⟨L,hL⟩ := h.mean_bounded
  have hnorm (z : ℂ) (ω : Ω) : ‖Y z ω-μ z ω‖ ≤ K+L := by
    calc
      _ ≤ ‖Y z ω‖+‖μ z ω‖ := norm_sub_le _ _
      _ = Y z ω+μ z ω := by rw [Real.norm_eq_abs, abs_of_nonneg (h.output_bound z ω).1,
        Real.norm_eq_abs, abs_of_nonneg (h.mean_nonneg z ω)]
      _ ≤ _ := add_le_add (h.output_bound z ω).2 (hL z ω)
  have hFb (ξ : ℝ × ℝ) (ω : Ω) : ‖F ξ ω‖ ≤ a^2*((n:ℝ)^2*(K+L)) := by
    dsimp only [F]
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg a)]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg a)
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i hi => hnorm _ ω).trans_eq (by simp [sq]; ring))
  have havg (ω : Ω) : (∫ ξ, F ξ ω ∂windowShiftLaw a) = ∫ z in D, (Y z ω-μ z ω) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      obtain ⟨_,hy,hμ⟩ := h.outside z hz ω
      simp only [hy,hμ,sub_self])]
    exact window_grid_average ((h.joint_output.sub h.joint_mean).comp
      (measurable_id.prodMk measurable_const)) (fun z => hnorm z ω) ha han
      (fun z hz => by
        obtain ⟨_,hy,hμ⟩ := h.outside z (fun hzD => hz (h.bounded_D hzD)) ω
        change Y z ω-μ z ω=0
        simp only [hy,hμ,sub_self])
  let : IsProbabilityMeasure (windowShiftLaw a) := windowShiftLaw_probability ha
  have hfinite (ξ : ℝ × ℝ) :
      (∫ ω, W ω*Real.exp (θ*F ξ ω) ∂P) ≤
      (∫ ω, W ω ∂P) * Real.exp (128*K^2*θ^2*R^2) := by
    have ht := window_source_finite_mgf_at_starts h (window_centers_separated (n := n) hsep ha.le ξ)
      (mul_nonneg hθ (sq_nonneg a)) hWa (fun i => hWs _) hW0 hWb hK
    have he : (Fintype.card (Fin n × Fin n) : ℝ)*((θ*a^2)*K)^2/2 ≤ 128*K^2*θ^2*R^2 := by
      simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
      have hs : a^2 ≤ 16*R^2 := by nlinarith [h.radius_pos.trans_le h.radius_le]
      calc
        _ = (a*n)^2*a^2*θ^2*K^2/2 := by ring
        _ = 8*a^2*θ^2*K^2 := by rw [han]; ring
        _ ≤ 8*(16*R^2)*θ^2*K^2 := by gcongr
        _ = _ := by ring
    have ht' : (∫ ω, W ω*Real.exp (θ*F ξ ω) ∂P) ≤
        (∫ ω, W ω ∂P) * Real.exp ((Fintype.card (Fin n × Fin n) : ℝ)*((θ*a^2)*K)^2/2) := by
      simpa only [F, mul_assoc] using ht
    exact ht'.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (integral_nonneg hW0))
  have ht := window_jensen_mgf (Q := windowShiftLaw a) hmeas hFb hθ hWa hW0 hWb hfinite
  simpa only [havg] using ht

end
end SLEExactGauge
end
end OAI
