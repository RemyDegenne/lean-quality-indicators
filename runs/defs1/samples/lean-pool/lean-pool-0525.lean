section

@[expose] public section

noncomputable section

open Set Filter

open scoped Topology ContDiff

namespace NavierStokes.FlatZeroExtension

open FlatCutoff

variable {E F : Type*}

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Every actual tensor is bounded, with constants and losses allowed to
depend on its derivative order as well as the parameter point. -/
def LocalGaussianJets (c : ℝ) (U : Set E) (f : E × ℝ → F) : Prop :=
  ∀ n : ℕ, LocalGaussianBound c U (iteratedFDeriv ℝ n f)

end NavierStokes.FlatZeroExtension
end
end
end
