public section

namespace TauCeti

open Finset Polynomial

variable {ι F : Type*} [Fintype ι] [Field F] [Finite F] [DecidableEq F]

theorem weightDistribution_euclideanDual_eq_sum_div (w : ℕ) (C : Submodule F (ι → F)) :
    ((Submodule.euclideanDual C : Set (ι → F)).weightDistribution w : ℚ) =
      (∑ j ∈ range (Fintype.card ι + 1),
        ((C : Set (ι → F)).weightDistribution j : ℚ) *
          (krawtchouk (Nat.card F) (Fintype.card ι) w j : ℚ)) / Nat.card C := by
  have hcard : (Nat.card C : ℚ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := C)).ne'
  apply (eq_div_iff hcard).mpr
  rw [mul_comm]
  exact_mod_cast natCard_mul_weightDistribution_euclideanDual w C

end TauCeti
end
