@[expose] public section

variable {α : Type*} {s t x y z : α} {S : Set α}

open Set

namespace Partition

section Order

variable [CompleteLattice α] {P Q : Partition s}

@[simp]
lemma mem_inf_iff {α : Type*} [Order.Frame α] {s a : α} {P Q : Partition s} :
    a ∈ P ⊓ Q ↔ a ≠ ⊥ ∧ ∃ p ∈ P, ∃ q ∈ Q, a = p ⊓ q :=
  and_comm

end Order
end Partition
end
