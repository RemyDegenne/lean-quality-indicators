public section

open Set Function MeasureTheory Measure Module Filter

open scoped ENNReal NNReal

namespace LipschitzWith

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
  {f : U → V} {s : Set U} {g : U → ℝ≥0} {K : ℝ≥0}

theorem ae_finite_fiber (hf : LipschitzWith K f) (hs : NullMeasurableSet s volume)
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).normDet) s) :
    ∀ᵐ y ∂μHE[finrank ℝ U], (s ∩ f ⁻¹' {y}).Finite := by
  have hsum := hf.ae_summable_fiber hs (g := fun _ ↦ 1) measurable_const (by simpa using hint)
  filter_upwards [hsum] with y hy
  exact Set.finite_coe_iff.mp (Finite.of_summable_const zero_lt_one hy)

end LipschitzWith
end
