namespace OAI

noncomputable section

open MeasureTheory MeasureTheory.Measure Real Metric Filter Topology Set ProbabilityTheory

open scoped ENNReal NNReal

namespace GeneralMahler

namespace Layers

lemma a_pos (z : ℝ) : 0 < a z := by
  rw [a_eq]
  apply (setIntegral_pos_iff_support_of_nonneg_ae ?_ (int_gap z).integrableOn).mpr
  · apply lt_of_lt_of_le (isOpen_Iio.measure_pos volume (Set.nonempty_Iio (a := z)))
    apply measure_mono
    intro x hx
    exact ⟨ne_of_gt (mul_pos (sub_pos.mpr hx) (phi_pos x)),show x ≤ z from le_of_lt hx⟩
  filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
  exact mul_nonneg (sub_nonneg.mpr hx) (phi_pos x).le

end Layers
end GeneralMahler
end
end OAI
