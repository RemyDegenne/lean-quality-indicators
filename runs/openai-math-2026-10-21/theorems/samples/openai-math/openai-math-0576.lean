namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem315.SliceEuclideanGenerator

variable {α : Type*} [Fintype α] [DecidableEq α]

@[simp] theorem sample_apply (q : ℕ) (f : (α → ℝ) → ℝ) (S : State α q) :
    sample q f S = f (coordinates S) := rfl

end Problem315.SliceEuclideanGenerator
end
end OAI
