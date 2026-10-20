section

@[expose] public section

noncomputable section

open Set Filter MeasureTheory

open scoped Topology BigOperators ContDiff

namespace NavierStokesR3.PressureRecovery

open NavierStokes.ProblemStatement

open NavierStokes.SolutionDifference (spatialPartial)

open NavierStokes.SolutionDifference

open Comparison ConservativeDifference HarmonicTestFunctionals PressureFunctionals

theorem canonical_sum_continuousOn {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) (ψ : ComplexTest) :
    ContinuousOn (fun t => ∑ i : Fin 3, ∑ j : Fin 3,
      pressurePair i j (tensorDiff u v t i j) ψ) (Icc 0 T) :=
  continuousOn_finsetSum _ (fun i _ =>
    continuousOn_finsetSum _ (fun j _ => pressurePair_continuousOn H i j ψ))

end NavierStokesR3.PressureRecovery
end
end
end
