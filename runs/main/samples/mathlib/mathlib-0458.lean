public section

variable {α β γ : Sort*}

variable (α)

variable {α}

open Relator

variable (R : α → β → Prop)

theorem biTotal_iff_isEmpty_right [IsEmpty α] : BiTotal R ↔ IsEmpty β := by
  simp only [BiTotal, leftTotal_empty, rightTotal_iff_isEmpty_right, true_and]

end
