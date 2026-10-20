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

@[simp]
theorem edist_eq [DilationClass F α β] (f : F) (x y : α) :
    edist (f x) (f y) = ratio f * edist x y := by
  rw [ratio]; split_ifs with key
  · rcases DilationClass.edist_eq' f with ⟨r, hne, hr⟩
    replace hr := hr x y
    rcases key x y with h | h
    · simp only [hr, h, mul_zero]
    · simp [hr, h, hne]
  exact (DilationClass.edist_eq' f).choose_spec.2 x y

end Setup
end Dilation
end
end
