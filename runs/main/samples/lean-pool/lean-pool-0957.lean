@[expose] public section

namespace BGS.Markoff

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

lemma cageTraceBranchPolynomial_separable
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    (cageTraceBranchPolynomial : K[X]).Separable := by
  have h4 : (4 : K) ≠ 0 := by
    convert mul_ne_zero h2 h2 using 1
    norm_num
  have h9 : (9 : K) ≠ 0 := by
    convert mul_ne_zero h3 h3 using 1
    norm_num
  have hquot : (4 / 9 : K) ≠ 0 := div_ne_zero h4 h9
  have hsep : (X ^ 2 - C (4 / 9) : K[X]).Separable :=
    separable_X_pow_sub_C _ h2 hquot
  have hunit : IsUnit (C (9 : K) : K[X]) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr h9)
  have heq : (cageTraceBranchPolynomial : K[X]) =
      C (9 : K) * (X ^ 2 - C (4 / 9)) := by
    simp only [cageTraceBranchPolynomial, mul_sub]
    rw [← C_mul, mul_div_cancel₀ (4 : K) h9]
  rw [heq]
  exact hsep.unit_mul hunit

end
end BGS.Markoff
end
