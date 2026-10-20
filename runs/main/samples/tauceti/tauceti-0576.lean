public section

noncomputable section

open Filter MeasureTheory Matrix Metric Set TopologicalSpace

open scoped ContDiff Distributions ENNReal Gradient InnerProductSpace NNReal Topology

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}

variable [DecidableEq ι]

theorem UniformlyEllipticOn.ae_inv_value_le_mul_setIntegral_rpow
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        0 ≤ energyFormH1 a 0 0 u (v : W1p mu Omega 2))
    {m : ℝ} (hm : 0 < m) (hum : ∀ᵐ x ∂mu.restrict Omega, m ≤ W1p.value u x)
    {x₀ : EuclideanSpace ℝ ι} {R K p : ℝ} (hR : 0 < R)
    (hball : ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι))) (hK : 0 ≤ K) (hp : 0 < p)
    (hsub : ∀ w : W1p mu Omega 2,
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a 0 0 w (v : W1p mu Omega 2) ≤ 0) →
      ∀ᵐ x ∂mu.restrict (ball x₀ (R / 2)),
        W1p.value w x ≤ K *
          (∫ x in ball x₀ R, max (W1p.value w x) 0 ^ p ∂mu) ^ p⁻¹) :
    ∀ᵐ x ∂mu.restrict (ball x₀ (R / 2)),
      (W1p.value u x)⁻¹ ≤ K * (∫ x in ball x₀ R, (W1p.value u x)⁻¹ ^ p ∂mu) ^ p⁻¹ := by
  have hhalf : ball x₀ (R / 2) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
    (ball_subset_ball (half_le_self hR.le)).trans hball
  have humB : ∀ᵐ x ∂mu.restrict (ball x₀ R), m ≤ W1p.value u x :=
    ae_restrict_of_ae_restrict_of_subset hball hum
  -- `u⁻ᵖ ≤ m⁻ᵖ` is integrable on the ball, which has finite measure.
  have : IsFiniteMeasure (mu.restrict (ball x₀ R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hint : Integrable (fun x => (W1p.value u x)⁻¹ ^ p) (mu.restrict (ball x₀ R)) := by
    have hmeas : AEMeasurable (fun x => (W1p.value u x)⁻¹ ^ p) (mu.restrict Omega) :=
      ((Lp.aestronglyMeasurable (W1p.value u)).aemeasurable.inv).pow_const p
    refine (integrable_const ((m⁻¹) ^ p)).mono'
      (hmeas.aestronglyMeasurable.mono_measure (Measure.restrict_mono hball le_rfl)) ?_
    filter_upwards [humB] with x hx
    have hux : 0 < W1p.value u x := hm.trans_le hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) p)]
    exact Real.rpow_le_rpow (by positivity)
      (by simpa only [one_div] using one_div_le_one_div_of_le hm hx) hp.le
  -- The approximations `u / (u² + c²)`, with `c = m / (k + 2) ≤ m / 2`, are subsolutions.
  set c : ℕ → ℝ := fun k => m / ((k : ℝ) + 2)
  have hc : ∀ k, 0 < c k := fun k => by positivity
  have hcm : ∀ k, 2 * c k ≤ m := fun k => by
    simp only [c]
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hbound : ∀ k, ∀ᵐ x ∂mu.restrict (ball x₀ (R / 2)),
      invApprox (c k) (W1p.value u x) ≤
        K * (∫ x in ball x₀ R, (W1p.value u x)⁻¹ ^ p ∂mu) ^ p⁻¹ := by
    intro k
    have hF := contDiff_invApprox (hc k)
    have hF0 : invApprox (c k) 0 = 0 := by simp [invApprox]
    -- The bounds on `F'` and `F''` in the form required by `TauCeti.W1p.contDiffComp`.
    have hM : ∀ t, ‖deriv (invApprox (c k)) t‖₊ ≤ ((c k ^ 2)⁻¹).toNNReal := fun t => by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, Real.coe_toNNReal _ (by positivity)]
      exact abs_deriv_invApprox_le (hc k) t
    have hM' : ∀ t, ‖deriv (deriv (invApprox (c k))) t‖₊ ≤ (3 / c k ^ 3).toNNReal := fun t => by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, Real.coe_toNNReal _ (by positivity)]
      exact abs_deriv_deriv_invApprox_le (hc k) t
    have hval := W1p.value_contDiffComp_ae ENNReal.ofNat_ne_top (hF.of_le one_le_two) hM hF0 u
    have hw := hsub _ fun v hv => h.energyFormH1_contDiffComp_nonpos ha hu hF hM hM' hF0 hum
      (fun t ht => deriv_invApprox_nonpos (hc k) ((hcm k).trans ht))
      (fun t ht => deriv_deriv_invApprox_nonneg (hc k) ((hcm k).trans ht)) v hv
    have hle : ∫ x in ball x₀ R, max (W1p.value (W1p.contDiffComp ENNReal.ofNat_ne_top
          (hF.of_le one_le_two) hM hF0 u) x) 0 ^ p ∂mu ≤
        ∫ x in ball x₀ R, (W1p.value u x)⁻¹ ^ p ∂mu := by
      refine integral_mono_of_nonneg (ae_of_all _ fun x => by positivity) hint ?_
      filter_upwards [humB, ae_restrict_of_ae_restrict_of_subset hball hval] with x hx hvx
      have hux := invApprox_mem_Icc (c := c k) (hm.trans_le hx)
      rw [hvx, max_eq_left hux.1]
      exact Real.rpow_le_rpow hux.1 hux.2 hp.le
    filter_upwards [hw, ae_restrict_of_ae_restrict_of_subset hhalf hval] with x hx hvx
    rw [← hvx]
    refine hx.trans ?_
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (integral_nonneg fun x => Real.rpow_nonneg (le_max_right _ _) p)
        hle (inv_nonneg.2 hp.le)) hK
  filter_upwards [ae_all_iff.2 hbound, ae_restrict_of_ae_restrict_of_subset hhalf hum]
    with x hx hux
  have hlim : Tendsto c atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  exact le_of_tendsto' (tendsto_invApprox hlim (hm.trans_le hux)) hx

end PDE
end TauCeti
end
end
