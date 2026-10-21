namespace OAI

open Set Filter MeasureTheory

open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory

open scoped ENNReal NNReal Topology

noncomputable section

open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported

open scoped ENNReal NNReal Topology BoundedContinuousFunction

open scoped NNReal

open MeasureTheory Set Filter

open scoped Topology NNReal ENNReal

open scoped ENNReal NNReal Topology InnerProductSpace

open Set Filter Bornology

open MeasureTheory

open scoped ENNReal InnerProductSpace ComplexConjugate

open Set Filter

open scoped Topology ENNReal NNReal

open Set

open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap

open scoped Topology ENNReal NNReal InnerProductSpace

open scoped BoundedContinuousFunction

open Set MeasureTheory Filter

open Set Filter MeasureTheory Topology TopologicalSpace

open scoped ENNReal NNReal

open Set MeasureTheory ProbabilityTheory

open scoped ENNReal MeasureTheory ProbabilityTheory

open Set Filter Topology Bornology

open scoped InnerProductSpace

open Filter

open scoped Topology

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory

open scoped ENNReal NNReal Topology

namespace WeakHessian

open MeasureTheory Filter

open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma weakGradient_comp_contDiff_le (hfinite : FiniteOnBoundedSets m)
    {f : X → ℝ} (hf : LocalSobolev m f) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hfφ : LocallyL2 m (φ ∘ f)) {B : ℝ} (hB : ∀ᵐ x ∂m, |deriv φ (f x)| ≤ B) :
    ∀ᵐ x ∂m, weakGradient m (φ ∘ f) x ≤ |deriv φ (f x)| *weakGradient m f x :=
  (weakGradient_isMinimal (hf.comp_contDiff hfinite hφ hfφ hB).2).2 _
    ((weakGradient_isMinimal hf.2).1.comp_contDiff hf.1.aemeasurable hφ hB)

end WeakHessian
end
end OAI
