namespace P2MW.S_Matrix_exists_algEquiv_centralizer_forall_map_le_iff_apply_one_zero_eq_zero_of_squarefree

set_option autoImplicit false

namespace BorelStab

open Matrix

variable {N : ℕ} [NeZero N]

section Morita

variable (α : (Matrix (Fin 2) (Fin 2) (ZMod N)) →+* Module.End (ZMod N) (Fin 2 → Fin 2 → ZMod N)) (v₀ : (Fin 2 → Fin 2 → ZMod N)) (hv₀ : ∀ w : (Fin 2 → Fin 2 → ZMod N), ∃! a : (Matrix (Fin 2) (Fin 2) (ZMod N)), w = α a v₀)

noncomputable def cOf (β : Module.End (ZMod N) (Fin 2 → Fin 2 → ZMod N)) : (Matrix (Fin 2) (Fin 2) (ZMod N)) := (epsE α v₀ hv₀).symm (β v₀)

end Morita
end BorelStab
end P2MW.S_Matrix_exists_algEquiv_centralizer_forall_map_le_iff_apply_one_zero_eq_zero_of_squarefree
