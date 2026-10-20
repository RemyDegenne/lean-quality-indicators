@[expose] public section

noncomputable section

open MeasureTheory Set intervalIntegral Homogenization Filter Topology

open AVenhance.Infra.Torus

namespace AVenhance.Infra.Heat

/-- Closed box containing the support of the two-dimensional periodic heat cutoff. -/
def PeriodicCutoff.heatPeriodicCutoff2ClosedBox : Set (Vec 2) :=
  Set.pi Set.univ (fun _ : Fin 2 => Icc (-1 : ℝ) 1)

end AVenhance.Infra.Heat
end
end
