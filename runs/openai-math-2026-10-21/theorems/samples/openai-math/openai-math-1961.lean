namespace OAI

open MeasureTheory Set

open scoped ENNReal NNReal Topology ContDiff

noncomputable section

namespace CenteredDiskEndpoint

theorem localized_cancellation {b : Plane → Plane} {K : Plane → ℝ}
    (hb : Integrable b) (hzero : ∫ y, b y = 0)
    {L : ℝ≥0} (hK : LipschitzWith L K) (z : Plane) {s : ℝ}
    (hsupp : ∀ᵐ y, b y ≠ 0 → ‖y - z‖ ≤ s) :
    ‖∫ y, K y • b y‖ ≤ (L : ℝ) * s * ∫ y, ‖b y‖ := by
  have hbound : ∀ᵐ y, ‖(K y - K z) • b y‖ ≤ ((L : ℝ) * s) * ‖b y‖ := by
    filter_upwards [hsupp] with y hy
    by_cases hby : b y = 0
    · simp [hby]
    · rw [norm_smul]
      exact mul_le_mul_of_nonneg_right
        ((hK.norm_sub_le y z).trans (mul_le_mul_of_nonneg_left (hy hby) L.coe_nonneg))
        (norm_nonneg _)
  have hdiff : Integrable (fun y => (K y - K z) • b y) :=
    (hb.norm.smul ((L : ℝ) * s)).mono'
      ((hK.continuous.sub continuous_const).aestronglyMeasurable.smul hb.aestronglyMeasurable)
      hbound
  have hprod : Integrable (fun y => K y • b y) := by
    have h := hdiff.add (hb.smul (K z))
    change Integrable (fun y => (K y - K z) • b y + K z • b y) at h
    simpa only [← add_smul, sub_add_cancel] using h
  rw [← integral_smul_sub_const hb hprod hzero (K z)]
  calc
    ‖∫ y, (K y - K z) • b y‖ ≤ ∫ y, ((L : ℝ) * s) * ‖b y‖ :=
      norm_integral_le_of_norm_le (hb.norm.smul ((L : ℝ) * s)) hbound
    _ = (L : ℝ) * s * ∫ y, ‖b y‖ := integral_const_mul _ _

end CenteredDiskEndpoint
end
end OAI
