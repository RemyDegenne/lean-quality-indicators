namespace OAI

noncomputable section

open MeasureTheory Set

open scoped ENNReal

namespace Problem358.MidpointCoordinates

lemma volume_interior {d : ℕ} {K : Set (E d)} (hK : Convex ℝ K) :
    volume (interior K) = volume K :=
  measure_congr (interior_ae_eq_of_null_frontier (hK.addHaar_frontier volume))

end Problem358.MidpointCoordinates
end
end OAI
