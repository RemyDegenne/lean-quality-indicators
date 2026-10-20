@[expose] public section

noncomputable section

namespace NavierStokes.LocalSignedRequest

open Set Function Filter MeasureTheory

open WeightedClasses WeightedRadialPrimitive

open scoped ContDiff Topology Interval BigOperators

theorem SlowRegion.chartQ_pos {coord : ℝ} (U : SlowRegion coord) {x : Point}
    (hx : x.2.1 ∈ U.carrier) : 0 < MeanRankUpdate.chartQ coord x :=
  U.qlo_pos.trans_le (U.q_mem x.2.1 hx).1

end NavierStokes.LocalSignedRequest
end
end
