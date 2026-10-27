public section

namespace CFSG.OddStandard.Solomon75.FourPartner

open Equiv Equiv.Perm Subgroup

section Classes

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem disjoint_cls02 (c σ : Perm α) : Disjoint (cls0 c σ) (cls2 c σ) := by
  rw [Finset.disjoint_left]
  intro x h0 h2
  rw [mem_cls0] at h0
  rw [mem_cls2] at h2
  exact h2.2.1 h0.2

end Classes
end CFSG.OddStandard.Solomon75.FourPartner
end
