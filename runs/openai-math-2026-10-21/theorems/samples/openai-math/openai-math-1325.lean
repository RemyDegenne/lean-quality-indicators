namespace OAI

section

section

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma hasDerivAt_euclideanRadialMass (μ : FiniteMeasure BlowupNormalBundle) (a : Cover)
    {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    HasDerivAt (euclideanRadialMass μ a ε)
      (∫ z, 2 * r * radialDensitySlope a r ε z.1 ∂(μ : Measure BlowupNormalBundle)) r := by
  obtain ⟨K, hK, hb⟩ := smoothTransition_exists_deriv_bound
  have hs : Ioo (r - 1) (r + 1) ∈ 𝓝 r := Ioo_mem_nhds (by linarith) (by linarith)
  have hm (s : ℝ) : AEStronglyMeasurable
      (fun z : BlowupNormalBundle ↦ radialDensityWeight a s ε z.1) (μ : Measure BlowupNormalBundle) :=
    (integrable_euclideanRadialWeight μ a s ε).aestronglyMeasurable
  have hm' : AEStronglyMeasurable
      (fun z : BlowupNormalBundle ↦ 2 * r * radialDensitySlope a r ε z.1) (μ : Measure BlowupNormalBundle) :=
    ((integrable_euclideanRadialSlope μ a r ε).const_mul _).aestronglyMeasurable
  have hb' : ∀ᵐ z ∂(μ : Measure BlowupNormalBundle), ∀ s ∈ Ioo (r - 1) (r + 1),
      ‖2 * s * radialDensitySlope a s ε z.1‖ ≤ 2 * (|r| + 1) * K / ε := by
    filter_upwards [] with z s hs
    have hsr : |s| ≤ |r| + 1 := by
      rw [abs_le]
      constructor <;> nlinarith [le_abs_self r, neg_abs_le r, hs.1, hs.2]
    have hsl : |radialDensitySlope a s ε z.1| ≤ K / ε := by
      simp only [radialDensitySlope, abs_div, abs_of_pos hε]
      exact div_le_div_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hb ((s ^ 2 - ‖(z.1 : Cover) - a‖ ^ 2) / ε)) hε.le
    simp only [Real.norm_eq_abs, abs_mul, show |(2 : ℝ)| = 2 from by norm_num]
    calc
      2 * |s| * |radialDensitySlope a s ε z.1| ≤ 2 * (|r| + 1) * (K / ε) :=
        mul_le_mul (by nlinarith) hsl (abs_nonneg _) (by positivity)
      _ = _ := by ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs (Eventually.of_forall hm)
    (integrable_euclideanRadialWeight μ a r ε) hm' hb' (integrable_const _)
    (Eventually.of_forall fun z s _ ↦ hasDerivAt_radialDensityWeight a z.1 s ε)).2

end CubicTorus
end
end
end
end OAI
