namespace OAI

open Set Filter MeasureTheory

open scoped ENNReal NNReal Topology

section InlinedFile0

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

lemma gamma_add_right (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {f g h : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g) (hh : LocalSobolev m h) :
    gamma m f (fun x => g x+h x) =ᵐ[m] (fun x => gamma m f g x+gamma m f h x) := by
  filter_upwards [gamma_add_left hfinite hpar hg hh hf,gamma_comm (m := m) f (fun x => g x+h x),
    gamma_comm (m := m) g f,gamma_comm (m := m) h f] with x hx h1 h2 h3
  rw [h1,hx,h2,h3]

end WeakHessian
end
end InlinedFile0
end OAI
