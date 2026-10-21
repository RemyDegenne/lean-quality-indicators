namespace OAI

section

open Set MeasureTheory Filter

open scoped InnerProductSpace Topology NNReal

open Set Filter

open scoped Topology NNReal

open Set MeasureTheory Filter

open scoped Topology NNReal ENNReal

open scoped ENNReal

open scoped InnerProductSpace ContDiff Topology

open scoped ENNReal

open Set MeasureTheory Filter

open scoped ENNReal Topology

open Set MeasureTheory Filter

open scoped InnerProductSpace Topology

noncomputable section

namespace UniformMoment

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

section Ball

variable [MeasurableSpace E] [BorelSpace E]

variable (μ : Measure E) [IsFiniteMeasureOnCompacts μ]

lemma exists_ballMoment_lower [μ.IsOpenPosMeasure] [Nontrivial E] :
    ∃ c : ℝ, 0 < c ∧ ∀ y : E, c*‖y‖ ≤ ballMoment μ y := by
  have hne : (Metric.sphere (0:E) 1).Nonempty := by
    obtain ⟨y,hy⟩ := exists_norm_eq E (show (0:ℝ) ≤ 1 by norm_num)
    exact ⟨y, by simpa [Metric.mem_sphere, dist_zero_right] using hy⟩
  obtain ⟨y,hy,hm⟩ := (isCompact_sphere (0:E) 1).exists_isMinOn hne
    (continuous_ballMoment μ).continuousOn
  have hyn : ‖y‖=1 := by simpa [Metric.mem_sphere, dist_zero_right] using hy
  refine ⟨ballMoment μ y, ballMoment_pos_of_norm_one μ hyn, ?_⟩
  intro z
  by_cases hz : z=0
  · simp [hz, ballMoment]
  have hnz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  let w : E := ‖z‖⁻¹ • z
  have hwn : ‖w‖=1 := by simp [w, norm_smul, hnz]
  have hw : w ∈ Metric.sphere (0:E) 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using hwn
  have hh : ballMoment μ y ≤ ballMoment μ w := hm hw
  have hz' : ‖z‖ • w = z := by simp [w, smul_smul, hnz]
  calc
    ballMoment μ y*‖z‖ ≤ ‖z‖*ballMoment μ w := by nlinarith [norm_nonneg z]
    _ = ballMoment μ (‖z‖ • w) := by
      rw [ballMoment_smul μ ‖z‖ w, abs_of_nonneg (norm_nonneg z)]
    _ = ballMoment μ z := by rw [hz']

end Ball
end UniformMoment
end
end
end OAI
