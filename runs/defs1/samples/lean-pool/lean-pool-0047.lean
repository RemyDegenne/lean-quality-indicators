open Complex MeasureTheory ProbabilityTheory

@[expose] public noncomputable section CarlsonNewtonTaylor

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

/-- The node vector obtained by placing `x` and `y` before a vector of `n` nodes. -/
def prependTwoNewtonNodes (x y : ℂ) (z : Fin n → ℂ) : Fin (n + 2) → ℂ :=
  Fin.cons x (Fin.cons y z)

end DirichletTransform
end CarlsonNewtonTaylor
