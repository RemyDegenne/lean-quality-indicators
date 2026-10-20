@[expose] public section

open Equiv Equiv.Perm List

variable {α : Type*}

namespace Equiv.Perm

section Fintype

variable [Fintype α] [DecidableEq α] (p : Equiv.Perm α) (x : α)

variable {p} {x}

theorem toList_formPerm_isRotated_self (l : List α) (hl : 2 ≤ l.length) (hn : Nodup l) (x : α)
    (hx : x ∈ l) : toList (formPerm l) x ~r l := by
  obtain ⟨k, hk, rfl⟩ := get_of_mem hx
  have hr : l ~r l.rotate k := ⟨k, rfl⟩
  rw [formPerm_eq_of_isRotated hn hr]
  rw [get_eq_get_rotate l k k]
  simp only [Nat.mod_eq_of_lt k.2, tsub_add_cancel_of_le (le_of_lt k.2), Nat.mod_self]
  rw [toList_formPerm_nontrivial]
  · simp
  · simpa using hl
  · simpa using hn

end Fintype
end Equiv.Perm
end
