@[expose] public section

attribute [local instance] Classical.propDecidable

open Finset

variable {T : Type*} [Inhabited T]

variable {I : Type*}

variable [IST : IndexedLOrder I T]

local notation  lhs "<[" i "]" rhs => IndexedLOrder.ltAt i lhs rhs

local notation  lhs "≤[" i "]" rhs => IndexedLOrder.leAt i lhs rhs

namespace IndexedLOrder

variable (σ : Finset T) (C : Finset I)

lemma sigma_nonempty_of_room {σ : Finset T} {C : Finset I} (h : isRoom σ C) : σ.Nonempty  := by
  rw [← Finset.card_pos, h.2.symm]
  exact Finset.card_pos.2 (Nonempty_of_Dominant h.1)

end IndexedLOrder
end
