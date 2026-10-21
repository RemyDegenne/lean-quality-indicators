namespace OAI

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory

open scoped Topology BigOperators ENNReal NNReal

namespace FKCRT.TreeCoding

local instance : MeasurableSpace C(unitInterval, ℝ) := borel _

local instance : BorelSpace C(unitInterval, ℝ) := ⟨rfl⟩

lemma normalized_integral_stability {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {k l F : Ω → ℝ} {M a : ℝ}
    (hk : Integrable k μ) (hl : Integrable l μ)
    (hl0 : ∀ᵐ ω ∂μ, 0 ≤ l ω)
    (hK : 0 < ∫ ω, k ω ∂μ) (hL : 0 < ∫ ω, l ω ∂μ)
    (hF : AEStronglyMeasurable F μ) (hM : 0 ≤ M)
    (hFM : ∀ᵐ ω ∂μ, |F ω| ≤ M)
    (ha : ∫ ω, |k ω-l ω| ∂μ ≤ a) :
    |(∫ ω, F ω*k ω ∂μ)/(∫ ω, k ω ∂μ) -
      (∫ ω, F ω*l ω ∂μ)/(∫ ω, l ω ∂μ)| ≤
      2*M*a/(∫ ω, k ω ∂μ) := by
  have hFk : Integrable (fun ω => F ω*k ω) μ :=
    (hk.norm.const_mul M).mono' (hF.mul hk.aestronglyMeasurable) (by
      filter_upwards [hFM] with ω hω
      simpa only [Real.norm_eq_abs,abs_mul] using mul_le_mul_of_nonneg_right hω (abs_nonneg (k ω)))
  have hFl : Integrable (fun ω => F ω*l ω) μ :=
    (hl.norm.const_mul M).mono' (hF.mul hl.aestronglyMeasurable) (by
      filter_upwards [hFM] with ω hω
      simpa only [Real.norm_eq_abs,abs_mul] using mul_le_mul_of_nonneg_right hω (abs_nonneg (l ω)))
  let K := ∫ ω, k ω ∂μ
  let L := ∫ ω, l ω ∂μ
  let A := ∫ ω, F ω*k ω ∂μ
  let D := ∫ ω, F ω*l ω ∂μ
  have hAD : |A-D| ≤ M*a := by
    rw [show A-D = ∫ ω, F ω*(k ω-l ω) ∂μ by
      simp only [A,D,mul_sub,integral_sub hFk hFl]]
    calc
      _ ≤ ∫ ω, |F ω*(k ω-l ω)| ∂μ := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun ω => F ω*(k ω-l ω))
      _ ≤ ∫ ω, M*|k ω-l ω| ∂μ := by
        apply integral_mono_ae
        · simpa only [mul_sub, Pi.sub_apply, Real.norm_eq_abs] using (hFk.sub hFl).norm
        · exact (hk.sub hl).norm.const_mul M
        · filter_upwards [hFM] with ω hω
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right hω (abs_nonneg _)
      _ ≤ M*a := by rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left ha hM
  have hKL : |L-K| ≤ a := by
    calc
      _ = |∫ ω, k ω-l ω ∂μ| := by rw [integral_sub hk hl]; exact abs_sub_comm _ _
      _ ≤ ∫ ω, |k ω-l ω| ∂μ := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun ω => k ω-l ω)
      _ ≤ a := ha
  have hD : |D| ≤ M*L := by
    calc
      _ ≤ ∫ ω, |F ω*l ω| ∂μ := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun ω => F ω*l ω)
      _ ≤ ∫ ω, M*l ω ∂μ := by
        apply integral_mono_ae hFl.norm (hl.const_mul M)
        filter_upwards [hFM,hl0] with ω hω hlω
        change |F ω*l ω| ≤ M*l ω
        rw [abs_mul,abs_of_nonneg hlω]
        exact mul_le_mul_of_nonneg_right hω hlω
      _ = M*L := integral_const_mul _ _
  have hA0 : 0 ≤ a := (integral_nonneg (fun _ => abs_nonneg _)).trans ha
  have hK' : K ≠ 0 := hK.ne'
  have hL' : L ≠ 0 := hL.ne'
  have he : A/K-D/L = (A-D)/K + D*(L-K)/(K*L) := by
    field_simp [hK',hL']
    ring
  change |A/K-D/L| ≤ 2*M*a/K
  rw [he]
  calc
    _ ≤ |(A-D)/K| + |D*(L-K)/(K*L)| := abs_add_le _ _
    _ = |A-D|/K + |D| *|L-K|/(K*L) := by
      rw [abs_div,abs_div,abs_mul,abs_of_pos hK,abs_of_pos (mul_pos hK hL)]
    _ ≤ (M*a)/K + (M*L)*a/(K*L) := by
      exact add_le_add (div_le_div_of_nonneg_right hAD hK.le)
        (div_le_div_of_nonneg_right (mul_le_mul hD hKL (abs_nonneg _) (by positivity))
          (mul_pos hK hL).le)
    _ = _ := by field_simp [hK',hL']; ring

end FKCRT.TreeCoding
end
end OAI
