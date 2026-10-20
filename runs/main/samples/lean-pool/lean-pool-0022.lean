@[expose] public section

noncomputable section

open scoped ContDiff ENNReal

open MeasureTheory Homogenization AVenhance.FaaDiBruno

open AVenhance.Infra.Section4 AVenhance.Infra.Ergodic AVenhance.Infra.Torus

namespace AVenhance.Infra.Section5

theorem slowWordSplits_map_directions (w : List (Fin 2)) :
    directionalSplits (w.map basisVec) =
      (slowWordSplits w).map (fun p => (p.1.map basisVec, p.2.map basisVec)) := by
  induction w with
  | nil => rfl
  | cons i w ih => simp [directionalSplits, slowWordSplits, ih, List.map_map, Function.comp_def]

end AVenhance.Infra.Section5
end
end
