@[expose] public section

noncomputable section

open Set Filter Function

open scoped Manifold Topology

variable {𝕜 E M H E' M' H' : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] [TopologicalSpace M] {n : WithTop ℕ∞}
  (f f' : OpenPartialHomeomorph M H)
  {I : ModelWithCorners 𝕜 E H} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  [TopologicalSpace M'] {I' : ModelWithCorners 𝕜 E' H'} {s t : Set M}

section ExtendedCharts

open OpenPartialHomeomorph

variable [ChartedSpace H M] [ChartedSpace H' M']

open IsManifold

variable (𝕜)

theorem ext_chart_model_space_apply {x y : E} : extChartAt 𝓘(𝕜, E) x y = y :=
  rfl

end ExtendedCharts
end
end
