namespace P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem

set_option autoImplicit false

namespace MacaulayCL

variable (n : ℕ)

variable {n}

section Compression

variable (i c : Fin (n + 1))

def pot (A : Finset (Fin (n + 1) →₀ ℕ)) : ℕ := ∑ u ∈ A, wt c u

end Compression
end MacaulayCL
end P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem
