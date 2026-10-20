@[expose] public section

open MeasureTheory Set

open scoped ENNReal NNReal ComplexConjugate

namespace QuadraticCarleson

theorem annularQuadraticKernel_correlation_le_ordered
    {a a' b b' : ℝ → ℂ} {R S H D u lam μ : ℝ}
    (hR : 0 < R) (hS : 0 < S) (hRS : R ≤ S) (hH : 0 < H) (hD : 0 ≤ D)
    (hu : 0 < u) (hu1 : u ≤ 1) (hdecay : 1 ≤ H * u ^ 5)
    (hlam : H ≤ lam * R ^ 2) (hlam' : lam * R ^ 2 ≤ 4 * H)
    (hμ : 0 ≤ μ) (hμ' : μ * S ^ 2 ≤ 4 * H)
    (ha : ∀ t, HasDerivAt a (a' t) t) (ha' : Continuous a')
    (hb : ∀ t, HasDerivAt b (b' t) t) (hb' : Continuous b')
    (hasupp : Function.support a ⊆ Icc (R / 4) R)
    (hbsupp : Function.support b ⊆ Icc (S / 4) S)
    (hab : ∀ t, ‖a t‖ ≤ D / R) (hab' : ∀ t, ‖a' t‖ ≤ D / R ^ 2)
    (hbb : ∀ t, ‖b t‖ ≤ D / S) (hbb' : ∀ t, ‖b' t‖ ≤ D / S ^ 2)
    (x y : ℝ) :
    ‖∫ t, annularQuadraticKernel a lam (x - t) *
      conj (annularQuadraticKernel b μ (y - t))‖ ≤
      quadraticFixedHeightMajorant (2 * D ^ 2) u S (x - y) := by
  let p : ℝ → ℂ := fun t ↦ a (x - t) * conj (b (y - t))
  let p' : ℝ → ℂ := fun t ↦
    (-a' (x - t)) * conj (b (y - t)) + a (x - t) * conj (-b' (y - t))
  let P : ℝ := 2 * D ^ 2 / (R * S)
  have hac : Continuous a := continuous_iff_continuousAt.mpr (fun t ↦ (ha t).continuousAt)
  have hbc : Continuous b := continuous_iff_continuousAt.mpr (fun t ↦ (hb t).continuousAt)
  have hpa (t : ℝ) : HasDerivAt (fun t ↦ a (x - t)) (-a' (x - t)) t := by
    simpa only [Function.comp_def, zero_sub, neg_one_smul] using
      (ha (x - t)).scomp t ((hasDerivAt_const t x).sub (hasDerivAt_id t))
  have hpb (t : ℝ) : HasDerivAt (fun t ↦ b (y - t)) (-b' (y - t)) t := by
    simpa only [Function.comp_def, zero_sub, neg_one_smul] using
      (hb (y - t)).scomp t ((hasDerivAt_const t y).sub (hasDerivAt_id t))
  have hp (t : ℝ) : HasDerivAt p (p' t) t := (hpa t).mul (hpb t).star
  have hp' : Continuous p' := by
    exact ((ha'.comp (continuous_const.sub continuous_id)).neg.mul
      (Complex.continuous_conj.comp (hbc.comp (continuous_const.sub continuous_id)))).add
      ((hac.comp (continuous_const.sub continuous_id)).mul
        (Complex.continuous_conj.comp (hb'.comp (continuous_const.sub continuous_id)).neg))
  have hsupp : Function.support p ⊆
      {t | R / 4 ≤ x - t ∧ x - t ≤ R ∧ 0 ≤ y - t ∧ y - t ≤ S} := by
    intro t ht
    have hat : a (x - t) ≠ 0 := by
      intro hz
      exact ht (by simp [p, hz])
    have hbt : b (y - t) ≠ 0 := by
      intro hz
      exact ht (by simp [p, hz])
    exact ⟨(hasupp hat).1, (hasupp hat).2,
      (by linarith [(hbsupp hbt).1]), (hbsupp hbt).2⟩
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hpnorm (t : ℝ) : ‖p t‖ ≤ P := by
    calc
      ‖p t‖ = ‖a (x - t)‖ * ‖b (y - t)‖ := by simp [p]
      _ ≤ (D / R) * (D / S) :=
        mul_le_mul (hab _) (hbb _) (norm_nonneg _) (by positivity)
      _ = D ^ 2 / (R * S) := by ring
      _ ≤ P := by
        dsimp [P]
        rw [mul_div_assoc]
        nlinarith [div_nonneg (sq_nonneg D) (mul_pos hR hS).le]
  have hpdnorm (t : ℝ) : ‖p' t‖ ≤ P / R := by
    calc
      ‖p' t‖ ≤ ‖(-a' (x - t)) * conj (b (y - t))‖ +
          ‖a (x - t) * conj (-b' (y - t))‖ := norm_add_le _ _
      _ = ‖a' (x - t)‖ * ‖b (y - t)‖ + ‖a (x - t)‖ * ‖b' (y - t)‖ := by
        simp only [norm_mul, norm_neg, RCLike.norm_conj]
      _ ≤ (D / R ^ 2) * (D / S) + (D / R) * (D / S ^ 2) := by
        apply add_le_add
        · exact mul_le_mul (hab' _) (hbb _) (norm_nonneg _) (by positivity)
        · exact mul_le_mul (hab _) (hbb' _) (norm_nonneg _) (by positivity)
      _ = (D ^ 2 / (R * S)) * (1 / R + 1 / S) := by field_simp
      _ ≤ (D ^ 2 / (R * S)) * (1 / R + 1 / R) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl (one_div_le_one_div_of_le hR hRS))
          (by positivity)
      _ = P / R := by dsimp [P]; field_simp; ring
  have h := norm_integral_quadraticTTStar_fixed_height_supported lam μ x y hR hS hH hu hu1
    hdecay hμ hRS hlam hlam' hμ' hp hp' hP hsupp hpnorm hpdnorm
  have hPR : P * R = (2 * D ^ 2) / S := by dsimp [P]; field_simp
  simp_rw [annularQuadraticKernel_mul_conj]
  simpa only [quadraticFixedHeightMajorant, hPR, abs_sub_comm y x, p] using h

end QuadraticCarleson
end
