@[expose] public section

noncomputable section

namespace NavierStokes.EndpointCoordinates

open Set Filter Function

open scoped Topology ContDiff

open SimilarityCoordinates

theorem composition_endpoint_smoothAt {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) {x : ProblemStatement.Space}
    (hx : x 2 ≠ 0) {f : Chart → V}
    (hf : ContDiffAt ℝ ∞ f (cartesianExtension h (1, x))) :
    ContDiffAt ℝ ∞ (fun p => f (cartesianExtension h p)) (1, x) :=
  composition_smoothAt hh hh1 (cartesian_endpoint_mem hh hh1 hx) hf

end NavierStokes.EndpointCoordinates
end
end
