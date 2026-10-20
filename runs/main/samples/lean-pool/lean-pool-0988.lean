@[expose] public section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

section Datum

attribute [instance] MultiplicityDatum.base_finite

theorem MultiplicityDatum.ae_norm_le_bound {𝕜 : Type*} [RCLike 𝕜]
    (D : MultiplicityDatum 𝕜) :
    ∀ᵐ p ∂D.measure, ‖p.1‖ ≤ D.bound := by
  rw [ae_iff]
  have hmeas : MeasurableSet {p : ℂ × ℕ | ¬ ‖p.1‖ ≤ D.bound} :=
    (measurableSet_le (measurable_norm.comp measurable_fst) measurable_const).compl
  rw [MultiplicityDatum.measure, sliceSum_apply _ hmeas, ENNReal.tsum_eq_zero]
  intro k
  have hfib : {z : ℂ | (z, k) ∈ {p : ℂ × ℕ | ¬ ‖p.1‖ ≤ D.bound}} = {z : ℂ | D.bound < ‖z‖} := by
    refine Set.ext fun z => ?_
    simp only [Set.mem_ofPred_eq, not_le]
  rw [hfib, Measure.restrict_apply (measurableSet_lt measurable_const measurable_norm)]
  exact measure_mono_null Set.inter_subset_left D.base_supported

end Datum
end TauCeti
end
