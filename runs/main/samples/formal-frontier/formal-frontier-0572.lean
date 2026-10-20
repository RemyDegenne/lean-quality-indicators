set_option warningAsError true

@[expose] public section

open scoped Matrix

namespace Matrix

universe u

theorem rightRowCompletionGL_inv_zero (R : Type u) [Ring R]
    {m : ℕ} (a b : Fin (m + 1) → R)
    (hb : dotProductBilin R Rᵐᵒᵖ a b = 1)
    (e : LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a) ≃ₗ[Rᵐᵒᵖ] (Fin m → R)) :
    (fun i ↦ ((rightRowCompletionGL R a b hb e)⁻¹).val i 0) = b := by
  rw [rightRowCompletionGL_inv_val]
  exact rightRowCompletionInv_zero R a b hb e

end Matrix
end
