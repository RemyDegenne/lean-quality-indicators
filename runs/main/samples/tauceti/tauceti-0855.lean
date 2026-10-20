public section

namespace TauCeti

namespace PDE

open Matrix

section BilinearForm

variable {n : Type*} [Fintype n]

lemma abs_dotProduct_coefficientSymmetricPart_mulVec_le {A : Matrix n n ℝ} {Lam : ℝ}
    (hA : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (η ξ : EuclideanSpace ℝ n) :
    |η ⬝ᵥ (coefficientSymmetricPart A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖ := by
  classical
  rw [← matrixBilinearForm_apply, matrixBilinearForm_coefficientSymmetricPart_apply]
  have hηξ : ‖matrixBilinearForm A η ξ‖ ≤ Lam * ‖η‖ * ‖ξ‖ :=
    norm_matrixBilinearForm_le_of_upper_bound A hA η ξ
  have hξη : ‖matrixBilinearForm A ξ η‖ ≤ Lam * ‖η‖ * ‖ξ‖ := by
    rw [mul_right_comm]
    exact norm_matrixBilinearForm_le_of_upper_bound A hA ξ η
  have hsum :
      ‖matrixBilinearForm A η ξ + matrixBilinearForm A ξ η‖
        ≤ 2 * (Lam * ‖η‖ * ‖ξ‖) := by
    calc
      ‖matrixBilinearForm A η ξ + matrixBilinearForm A ξ η‖
          ≤ ‖matrixBilinearForm A η ξ‖ + ‖matrixBilinearForm A ξ η‖ := norm_add_le _ _
      _ ≤ Lam * ‖η‖ * ‖ξ‖ + Lam * ‖η‖ * ‖ξ‖ := add_le_add hηξ hξη
      _ = 2 * (Lam * ‖η‖ * ‖ξ‖) := by ring
  rw [abs_div]
  rw [abs_of_pos (a := (2 : ℝ)) two_pos]
  exact (div_le_iff₀' two_pos).2 (by
    simpa [Real.norm_eq_abs] using hsum)

end BilinearForm
end PDE
end TauCeti
end
