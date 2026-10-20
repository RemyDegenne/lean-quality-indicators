@[expose] public section

open Relation

open scoped List

universe u v w

variable {α : Type u}

attribute [local simp] List.append_eq_has_append

namespace FreeGroup

variable {L L₁ L₂ L₃ : List (α × Bool)}

@[to_additive]
theorem Red.Step.invRev {L₁ L₂ : List (α × Bool)} (h : Red.Step L₁ L₂) :
    Red.Step (FreeGroup.invRev L₁) (FreeGroup.invRev L₂) := by
  obtain ⟨a, b, x, y⟩ := h
  simp [FreeGroup.invRev]

end FreeGroup
end
