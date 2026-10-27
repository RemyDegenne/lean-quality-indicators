public section

set_option maxRecDepth 100000

namespace CFSG.Quasithin.SmithC27

open Equiv Equiv.Perm

open scoped Pointwise

section PermCount

variable {α : Type*} [DecidableEq α] [Fintype α]

theorem card_stabilizer_coe_finset (s : Finset α) :
    Nat.card (MulAction.stabilizer (Perm α) (s : Set α)) =
      ∏ i : Bool, (Fintype.card {a // decide (a ∈ s) = i}).factorial := by
  have e : MulAction.stabilizer (Perm α) (s : Set α) ≃
      {g : Perm α // (fun a => decide (a ∈ s)) ∘ g = fun a => decide (a ∈ s)} :=
    Equiv.subtypeEquivRight fun g => by
      rw [mem_stabilizer_coe_finset_iff, funext_iff]
      simp only [Function.comp_apply, decide_eq_decide]
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, DomMulAct.stabilizer_card]

end PermCount
end CFSG.Quasithin.SmithC27
end
