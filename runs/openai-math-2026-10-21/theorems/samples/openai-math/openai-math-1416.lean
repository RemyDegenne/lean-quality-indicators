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

open Set Filter MeasureTheory

open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

namespace WeakHessian

open MeasureTheory Filter Set

open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma IsTestPlan.integrable_eval_bounded {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {f : X → ℝ} (hf : AEMeasurable f m) {B : ℝ} (hB : ∀ᵐ x ∂m, |f x| ≤ B) (t : Time) :
    Integrable (fun γ => f (γ t)) π := by
  let : IsProbabilityMeasure π := hπ.1
  exact (integrable_const B).mono' (hπ.aemeasurable_eval hf t).aestronglyMeasurable
    ((hπ.ae_eval_of_ae hB t).mono fun γ hγ => by simpa only [Real.norm_eq_abs] using hγ)

end WeakHessian
end
end OAI
