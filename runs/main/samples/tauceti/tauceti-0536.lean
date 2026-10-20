public section

open Set Function MeasureTheory Measure Module

open scoped NNReal ENNReal symmDiff

namespace TauCeti

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
  {f : U → V} {s : Set U} {g : U → ℝ≥0∞}

theorem tsum_fiber_inter_setOf_regular_ae_eq (s : Set U) (g : U → ℝ≥0∞)
    {K : ℝ≥0} (hf : LipschitzWith K f) :
    (fun y ↦ ∑' x : ↥((s ∩ {x | DifferentiableAt ℝ f x ∧
      (fderiv ℝ f x).normDet ≠ 0}) ∩ f ⁻¹' {y}), g x) =ᵐ[μHE[finrank ℝ U]]
      fun y ↦ ∑' x : ↥(s ∩ f ⁻¹' {y}), g x := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp
    hf.euclideanHausdorffMeasure_image_compl_setOf_regular] with y hy
  apply tsum_congr_set_coe g
  ext x
  have hx : f x = y → DifferentiableAt ℝ f x ∧ (fderiv ℝ f x).normDet ≠ 0 :=
    fun h ↦ not_not.1 fun hx ↦ hy ⟨x, hx, h⟩
  simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff]
  aesop

end TauCeti
end
