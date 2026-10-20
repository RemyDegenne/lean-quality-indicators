@[expose] public section

noncomputable section

open Bornology Function Set Topology Metric

open scoped ENNReal NNReal

@[inherit_doc] infixl:25 " →ᵈ " => Dilation

namespace Dilation

variable {α : Type*} {β : Type*} {γ : Type*} {F : Type*}

section Setup

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β]

variable [FunLike F α β]

open scoped Classical in
/-- The ratio of a dilation `f`. If the ratio is undefined (i.e., the distance between any two
points in `α` is either zero or infinity), then we choose one as the ratio. -/
def ratio [DilationClass F α β] (f : F) : ℝ≥0 :=
  if ∀ x y : α, edist x y = 0 ∨ edist x y = ⊤ then 1 else (DilationClass.edist_eq' f).choose

end Setup
end Dilation
end
end
