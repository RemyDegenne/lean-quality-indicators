namespace OAI

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation

namespace Tensor

variable {F X Y Z : Type*} [Field F]

namespace PolynomialApproximation

variable {T : Tensor F X Y Z} {r d D : ℕ}

theorem rank_normalized_eval (A : PolynomialApproximation T r d D)
    (t : F) (ht : t ≠ 0) :
    RankAtMost (fun x y z => (A.normalized x y z).eval t) r := by
  have h := (A.rank_bound.map (Polynomial.evalRingHom t)).scale ((t ^ d)⁻¹)
  change RankAtMost (fun x y z => (t ^ d)⁻¹ * (A.polynomial x y z).eval t) r at h
  have heq : (fun x y z => (t ^ d)⁻¹ * (A.polynomial x y z).eval t) =
      fun x y z => (A.normalized x y z).eval t := by
    funext x y z
    rw [A.polynomial_eq, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero d ht), one_mul]
  rw [heq] at h
  exact h

end PolynomialApproximation
end Tensor
end MatrixMultiplication.Foundation
end
end OAI
