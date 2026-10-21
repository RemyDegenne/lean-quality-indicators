namespace OAI

noncomputable section

open Set Filter

open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse

open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem actual_metric_word_difference_le {g h : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hh : SmoothPositiveOn h U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) (i j : Fin 2) (ds : List (Fin 2)) {epsilon : ℝ}
    (hjet : ‖iteratedFDeriv ℝ ds.length (fun q => g q i j-h q i j) p‖ ≤ epsilon) :
    |iteratedCoordPartial ds (fun q => g q i j) p-
      iteratedCoordPartial ds (fun q => h q i j) p| ≤ epsilon := by
  have hb := (norm_iteratedCoordPartial_le_jet ((hg.1 i j).sub (hh.1 i j)) hU ds hp).trans hjet
  rw [iteratedCoordPartial_sub_actual (hg.1 i j) (hh.1 i j) hU ds hp,
    Real.norm_eq_abs] at hb
  exact hb

end SmoothLocal.Pulse
end
end OAI
