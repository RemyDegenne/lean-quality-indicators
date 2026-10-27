set_option autoImplicit false

namespace CohCarrier

open Matrix CongruenceSubgroup Matrix.SpecialLinearGroup

open scoped MatrixGroups

section FrickeMat

variable (N : ℕ)

def frickeMat (A : SL(2, ℤ)) (h : (N : ℤ) ∣ A 1 0) : SL(2, ℤ) :=
  ⟨!![A 1 1, -(A 1 0 / N); -(N * A 0 1), A 0 0], by
    rw [Matrix.det_fin_two_of]
    have hdet := Matrix.SpecialLinearGroup.det_coe A
    rw [Matrix.det_fin_two] at hdet
    have hc : A 1 0 / N * N = A 1 0 := Int.ediv_mul_cancel h
    have hc' : A 1 0 / N * (N * A 0 1) = A 1 0 * A 0 1 := by rw [← mul_assoc, hc]
    rw [neg_mul_neg, hc']
    linear_combination hdet⟩

end FrickeMat
end CohCarrier
