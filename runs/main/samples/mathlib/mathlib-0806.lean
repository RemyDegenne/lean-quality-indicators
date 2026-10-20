public section

open Equiv Function Finset

variable {α β : Type*}

namespace Equiv.Perm

section CycleOf

variable {f g : Perm α} {x y : α}

@[simp] lemma support_cycleOf_nonempty [DecidableEq α] [Fintype α] :
    (cycleOf f x).support.Nonempty ↔ f x ≠ x := by
  rw [← two_le_card_support_cycleOf_iff, ← card_pos, ← Nat.succ_le_iff]
  exact ⟨fun h => Or.resolve_left h.eq_or_lt (card_support_ne_one _).symm, zero_lt_two.trans_le⟩

end CycleOf
end Equiv.Perm
end
