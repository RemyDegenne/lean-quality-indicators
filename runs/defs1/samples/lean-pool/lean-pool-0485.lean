open Complex MeasureTheory ProbabilityTheory

@[expose] public noncomputable section CarlsonNewtonTaylor

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

/-- Carlson's unweighted Dirichlet average, obtained by setting every Dirichlet parameter
equal to one. -/
def carlsonUnweightedAverage (z : ι → ℂ) (f : ℂ → ℂ) : ℂ :=
  realCarlsonDirichletAverage (fun _ ↦ 1) z f

end DirichletTransform
end CarlsonNewtonTaylor
