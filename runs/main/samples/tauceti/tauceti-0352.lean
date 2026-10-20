public section

namespace TauCeti

open _root_.Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

variable [IsRealClosed R]

theorem irreducible_quadratic_eval_mul_pos {p : R[X]} (hp : Irreducible p)
    (hdeg : p.natDegree = 2) (a b : R) : 0 < p.eval a * p.eval b := by
  rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.mpr hp.ne_zero) with h | h
  · exact mul_pos_of_neg_of_neg
      ((irreducible_quadratic_eval_neg_iff_leadingCoeff_neg hp hdeg a).mpr h)
      ((irreducible_quadratic_eval_neg_iff_leadingCoeff_neg hp hdeg b).mpr h)
  · exact mul_pos ((irreducible_quadratic_eval_pos_iff_leadingCoeff_pos hp hdeg a).mpr h)
      ((irreducible_quadratic_eval_pos_iff_leadingCoeff_pos hp hdeg b).mpr h)

end TauCeti
end
