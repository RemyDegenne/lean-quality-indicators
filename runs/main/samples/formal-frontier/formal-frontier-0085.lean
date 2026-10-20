@[expose] public section

universe u v w x y

namespace KTheory.K0

variable (R : Type u) [Ring R]

theorem sub_eq_sub_iff_exists_free_stabilizer
    (P : Type v) [AddCommGroup P] [Module Rᵐᵒᵖ P]
    [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P]
    (Q : Type w) [AddCommGroup Q] [Module Rᵐᵒᵖ Q]
    [Module.Finite Rᵐᵒᵖ Q] [Module.Projective Rᵐᵒᵖ Q]
    (P' : Type x) [AddCommGroup P'] [Module Rᵐᵒᵖ P']
    [Module.Finite Rᵐᵒᵖ P'] [Module.Projective Rᵐᵒᵖ P']
    (Q' : Type y) [AddCommGroup Q'] [Module Rᵐᵒᵖ Q']
    [Module.Finite Rᵐᵒᵖ Q'] [Module.Projective Rᵐᵒᵖ Q'] :
    of R P - of R Q = of R P' - of R Q' ↔
      ∃ n : ℕ, Nonempty (((P × Q') × (Fin n → Rᵐᵒᵖ)) ≃ₗ[Rᵐᵒᵖ]
        ((P' × Q) × (Fin n → Rᵐᵒᵖ))) := by
  rw [sub_eq_sub_iff_add_eq_add, ← of_prod R P Q', ← of_prod R P' Q]
  exact of_eq_iff_exists_free_stabilizer R (P × Q') (P' × Q)

end KTheory.K0
end
