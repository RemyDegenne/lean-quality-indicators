namespace P2MW.S_MeasureTheory_volume_setOf_mvPolynomial_eval_eq_zero

set_option autoImplicit false

open MeasureTheory

theorem solution
    {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (hp : p ≠ 0) :
    volume {x : Fin n → ℝ | MvPolynomial.eval x p = 0} = 0 :=
  NullsetMvPolynomialSol.main n p hp

end P2MW.S_MeasureTheory_volume_setOf_mvPolynomial_eval_eq_zero
