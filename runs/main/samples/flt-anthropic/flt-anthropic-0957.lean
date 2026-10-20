namespace P2MW.S_Matrix_nonempty_linearEquiv_self_of_natCard_eq_pow_of_natCard_torsionBy

set_option autoImplicit false

universe u

namespace ASM21

namespace M2

section module

variable {ℓ : ℕ} (V : Type u) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V]

theorem sc_zero (c : ZMod ℓ) : sc V c (0 : V) = 0 := smul_zero _

end module
end M2
end ASM21
end P2MW.S_Matrix_nonempty_linearEquiv_self_of_natCard_eq_pow_of_natCard_torsionBy
