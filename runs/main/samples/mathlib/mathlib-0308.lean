@[expose] public section

open Function OrderDual

variable {ι α β : Type*} {π : ι → Type*}

scoped[symmDiff] infixl:100 " ∆ " => symmDiff

scoped[symmDiff] infixl:100 " ⇔ " => bihimp

open scoped symmDiff

section GeneralizedBooleanAlgebra

variable [GeneralizedBooleanAlgebra α] (a b c d : α)

@[simp]
theorem le_symmDiff_iff_left : a ≤ a ∆ b ↔ Disjoint a b := by
  refine ⟨fun h => ?_, fun h => h.symmDiff_eq_sup.symm ▸ le_sup_left⟩
  rw [symmDiff_eq_sup_sdiff_inf] at h
  exact disjoint_iff_inf_le.mpr (le_sdiff_right.1 <| inf_le_of_left_le h).le

end GeneralizedBooleanAlgebra
end
