@[expose] public section

namespace TriangleInflation

open Finset

noncomputable
section

attribute [instance] TriangleModel.fintypeX TriangleModel.fintypeY TriangleModel.fintypeZ

/-- Paper Definition 2.4: the ancestral-independence feasible set `I^AI_t`. -/
def AIFeasible (t : ℕ) (P : ThreeBit → ℝ) : Prop :=
  ∃ Γ : Assign t → ℝ, IsLaw Γ ∧ SymmetricLaw t Γ ∧
    pushforward Γ readDiagonal = tensorPow t P ∧
    InjectableMarginals t Γ P ∧ AncestralProducts t Γ P

end
end TriangleInflation
end
