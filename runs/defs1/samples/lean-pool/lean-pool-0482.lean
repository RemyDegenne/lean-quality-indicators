section

@[expose] public section

noncomputable section

open Set Filter Function MeasureTheory

open scoped Topology ContDiff BigOperators

namespace NavierStokes.PrimaryCovarianceBounds

noncomputable local instance : NormedAddCommGroup Mat2 :=
  inferInstanceAs (NormedAddCommGroup (Fin 2 → Fin 2 → ℝ))

noncomputable local instance : NormedSpace ℝ Mat2 :=
  inferInstanceAs (NormedSpace ℝ (Fin 2 → Fin 2 → ℝ))

/-- Normalized pair, defined pointwise by `PulseCovariance.normalizedColumn (P j).ψ (P j).x (P
j).t i`. -/
noncomputable def normalizedPair (P : Fin 2 → PartitionedCovariance.Pulse) : Mat2 :=
  fun i j => PulseCovariance.normalizedColumn (P j).ψ (P j).x (P j).t i

end NavierStokes.PrimaryCovarianceBounds
end
end
end
