namespace P2MW.S_CuspidalType_natCard_not_mem_center_and_charpoly_eq_X_sub_C_sq

set_option autoImplicit false

open Polynomial CuspidalType

namespace Ws23C2

open Polynomial Matrix

theorem card_nil (q : ℕ) [Fact q.Prime] :
    Nat.card {N : Matrix (Fin 2) (Fin 2) (ZMod q) // N ≠ 0 ∧ N * N = 0} = q ^ 2 - 1 := by
  rw [← Nat.card_eq_of_bijective _ nilOf_bijective, Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl, Fintype.card_prod, ZMod.card, Fintype.card_subtype_eq, sq]

end Ws23C2
end P2MW.S_CuspidalType_natCard_not_mem_center_and_charpoly_eq_X_sub_C_sq
