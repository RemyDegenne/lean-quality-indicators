namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Topology

open MeasureTheory Filter Set

open scoped Topology

open MeasureTheory ProbabilityTheory Filter Set

namespace SKFluctuations.Hierarchy

open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus

open scoped Topology NNReal ENNReal BigOperators

variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

theorem segmentResponseCost_integrable {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ) (tail pre : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a (pre++tail)) (v : Fin pre.length → ι → ℝ) (x : ι → ℝ) :
    Integrable (segmentResponseCost w φ A tail pre v x) (segmentLaw w φ tail pre x) := by
  have := segmentLaw_isProbability hw φ tail pre ha x
  obtain ⟨B,_,hB⟩ := segmentResponseCost_bound hw φ A tail pre ha v
  exact memLp_one_iff_integrable.mp (MemLp.of_bound
    (((segmentResponseCost_continuous hw φ A tail pre ha v).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable) B
    (ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs] using hB x p)))

end SKFluctuations.Hierarchy
end
end OAI
