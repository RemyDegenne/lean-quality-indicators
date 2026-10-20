public section

open Filter Function Topology

open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E E' H M : Type*}

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [NormedAddCommGroup E'] [NormedSpace ℝ E']

variable [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

variable [TopologicalSpace M] [ChartedSpace H M]

variable {f : M → ℝ} {x : M}

/-- The **Morse index** of a real-valued function at a point of a smooth manifold: the negative
index of inertia of the Hessian of its expression in the preferred extended chart.

As with `TauCeti.morseIndex` and `TauCeti.IsManifoldNondegenerateCriticalPoint`, the definition
carries no smoothness or boundary hypotheses and is available at every point. It is specifically
the index computed in the preferred extended chart; the results below prove germ locality and
invariance under transport of the model by a continuous linear equivalence. For a model with
boundary or corners the unconstrained Hessian can depend on the behaviour of the chart inverse
off `range I`, and it is not the boundary Morse condition, which is a different theory. -/
noncomputable def manifoldMorseIndex (I : ModelWithCorners ℝ E H) (f : M → ℝ) (x : M) : ℕ :=
  morseIndex (f ∘ (extChartAt I x).symm) (extChartAt I x x)

end TauCeti
end
end
