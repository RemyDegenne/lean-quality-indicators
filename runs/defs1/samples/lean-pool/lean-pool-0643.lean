open Complex MeasureTheory ProbabilityTheory Set Filter Metric

open scoped Topology

@[expose] public noncomputable section

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

/-- The entire-parameter regularized integer resolvent. Values outside
`carlsonResolventDomain` are unspecified; theorems only use it on that domain. -/
def continuedRegCarlsonResolvent (n : ℕ) (b z : ι → ℂ) (s : ℂ) : ℂ :=
  (exists_joint_regCarlsonResolvent (ι := ι) n).choose (b, fun i => i.elim s z)

end DirichletTransform
end
