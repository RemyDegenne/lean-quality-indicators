namespace OAI

section

open scoped Real

open MeasureTheory

open scoped Topology

open MeasureTheory FourierTransform Convolution

open scoped SchwartzMap

open MeasureTheory FourierTransform TemperedDistribution

open scoped SchwartzMap Topology

open MeasureTheory TemperedDistribution FourierTransform LineDeriv

open scoped SchwartzMap ContDiff

open Filter Function

open scoped SchwartzMap Topology ContDiff

open MeasureTheory FourierTransform TemperedDistribution

open scoped SchwartzMap Topology ContDiff

open MeasureTheory

open scoped Topology ContDiff

open Matrix

open scoped ContDiff Matrix.Norms.Elementwise

open scoped ContDiff Topology

noncomputable section

namespace DensityEnergy

open MeasureTheory Matrix WeightedCalculus Filter

open scoped ContDiff Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma henergy_nonneg {τ : Space ι → Matrix ι ι ℝ} (ht : ∀ x, (τ x).PosSemidef)
    {f : Space ι → ℝ} (hf : ContDiff ℝ ∞ f) (x : Space ι) : 0 ≤ henergy τ f x := by
  apply MomentMatrix.trace_conjugate_nonneg (ht x)
  ext i j
  exact MomentCoordinates.hess_symm hf x j i

end DensityEnergy
end
end
end OAI
