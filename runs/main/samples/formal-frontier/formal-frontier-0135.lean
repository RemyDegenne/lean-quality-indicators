set_option warningAsError true

@[expose] public section

open scoped Matrix

namespace Matrix

universe u

@[simp]
theorem rightRowCompletionGL_zero (R : Type u) [Ring R]
    {m : ℕ} (a b : Fin (m + 1) → R)
    (hb : dotProductBilin R Rᵐᵒᵖ a b = 1)
    (e : LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a) ≃ₗ[Rᵐᵒᵖ] (Fin m → R)) :
    (rightRowCompletionGL R a b hb e : Matrix (Fin (m + 1)) (Fin (m + 1)) R) 0 = a := by
  rw [rightRowCompletionGL_val, rightRowCompletion_zero]

end Matrix
end
