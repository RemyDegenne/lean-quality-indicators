namespace CFSG.FeitThompson

public section

set_option autoImplicit true

set_option maxSynthPendingDepth 3

open Subgroup

open scoped commutatorElement

variable {R : Type*} [Group R] {p i : ℕ} {H S : Subgroup R}

theorem commutatorChain_succ_lt (H : Subgroup R) [H.Normal] {n : ℕ}
    (hn : commutatorChain H n = ⊥) (hi : commutatorChain H i ≠ ⊥) :
    commutatorChain H (i + 1) < commutatorChain H i := by
  refine lt_of_le_of_ne (commutatorChain_succ_le H i) fun h => hi ?_
  have h1 : commutatorChain H (i + n) = commutatorChain H i := commutatorChain_add_of_succ_eq H h n
  have h2 : commutatorChain H (i + n) ≤ commutatorChain H n :=
    commutatorChain_antitone H (Nat.le_add_left n i)
  rw [hn, le_bot_iff] at h2
  rw [← h1, h2]

end
end CFSG.FeitThompson
