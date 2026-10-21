namespace OAI

open MeasureTheory ProbabilityTheory

namespace Invariant233.OrderedProductCoupling

theorem right_threshold_iCondIndepSet_iff_circle (P : Parameters) (u : ℕ → ℝ) :
    iCondIndepSet ((inferInstance : MeasurableSpace Endpoint).comap leftEndpoint)
      leftEndpoint_measurable.comap_le
      (fun i => {ω : Sample | u i ≤ rightEndpoint ω i}) (law P) ↔
    iCondIndepSet ((inferInstance : MeasurableSpace ProductModel.Base).comap circleLeftEndpoint)
      circleLeftEndpoint_measurable.comap_le
      (fun i => {ω : Sample | u i ≤ realEndpoint (circleRightEndpoint ω) i}) (law P) := by
  have hraw (i : ℕ) : MeasurableSet {ω : Sample | u i ≤ rightEndpoint ω i} :=
    measurableSet_le measurable_const ((measurable_pi_apply i).comp rightEndpoint_measurable)
  have hcircle (i : ℕ) :
      MeasurableSet {ω : Sample | u i ≤ realEndpoint (circleRightEndpoint ω) i} :=
    measurableSet_le measurable_const
      ((measurable_pi_apply i).comp (realEndpoint_measurable.comp circleRightEndpoint_measurable))
  exact (left_iCondIndepSet_iff_circle P _ hraw).trans
    (ObservationConditioning.iCondIndepSet_iff_of_events_ae_eq
      _ circleLeftEndpoint_measurable.comap_le (law P) _ _ hraw hcircle
      (right_threshold_event_ae_eq_circle P u))

end Invariant233.OrderedProductCoupling
end OAI
