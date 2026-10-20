@[expose] public noncomputable section

open Function Cardinal Set Equiv Order

universe u v w

namespace Ordinal

variable {α β γ : Type*} {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}

theorem mul_sub (a b c : Ordinal) : a * (b - c) = a * b - a * c := by
  obtain rfl | ha := eq_or_ne a 0
  · simp
  · refine eq_of_forall_ge_iff fun d ↦ ?_
    rw [sub_le, mul_le_iff_le_div ha, sub_le, mul_le_iff_le_div ha, mul_add_div _ ha]

end Ordinal
end
