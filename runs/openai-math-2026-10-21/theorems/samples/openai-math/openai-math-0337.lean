namespace OAI

open MeasureTheory Set

open scoped ENNReal NNReal Topology ContDiff

open scoped RealInnerProductSpace

open MeasureTheory Set Filter

open scoped Topology ENNReal

open scoped Real RealInnerProductSpace

open scoped Topology RealInnerProductSpace ContDiff

open scoped Topology Interval NNReal

open scoped Topology NNReal Real

open MeasureTheory Set Metric

open scoped ENNReal NNReal Topology

open scoped ENNReal NNReal

open Finset

open scoped ENNReal NNReal RealInnerProductSpace

open scoped ContDiff

open MeasureTheory Set Metric Filter

open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology

open MeasureTheory MeasureTheory.Measure Set Filter

open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff

open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace GeometricFilter

open Finset

theorem filt_tail {c : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A) (hc0 : ∀ i, 0 ≤ c i)
    (hcA : ∀ i, c i ≤ A) {b m : ℕ} (hbm : b ≤ m) :
    (∑ i ∈ Ico b (m+1), filt c i) ≤ 2*∑ i ∈ Ico b (m+1), c i+4*A := by
  have h1 := filt_tail_strong hc0 hbm
  have h2 := filt_le hA hcA b
  linarith

end GeometricFilter
end SignedDisk
end
end OAI
