@[expose] public section

noncomputable section

open Set Filter Function MeasureTheory

open scoped Topology ContDiff BigOperators

open NavierStokes.OutgoingProfile

namespace NavierStokes.NominalProfile

/-- Base E, given by `splice matchFraction (preparedE F C T li oldf) F.E`. -/
noncomputable def baseE (F : Profile) (C T : ℝ) (li : ℝ → ℝ) (oldf : Field) : Field :=
  splice matchFraction (preparedE F C T li oldf) F.E

end NavierStokes.NominalProfile
end
end
