namespace OAI

open MeasureTheory

namespace DefocusingNLS

theorem regularizedSlowSolution_shift_relation (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 < x.re) :
    x * (q + 1) * regularizedSlowSolution (q + 2) (m + 2) x +
      (x - (m : ℂ)) * regularizedSlowSolution (q + 1) (m + 1) x -
        regularizedSlowSolution q m x = 0 := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have hq' : 0 < (q + 1).re := by change 0 < q.re + 1; linarith
  have hq'' : 0 < (q + 2).re := by change 0 < q.re + 2; linarith
  rw [regularizedSlowSolution_contiguous q m x hq hx.le hx0,
    regularizedSlowSolution_eq_euler_complex (q + 2) (m + 2) x hq'' hx,
    regularizedSlowSolution_eq_euler_complex (q + 1) (m + 1) x hq' hx,
    regularizedSlowSolution_eq_euler_complex (q + 1) m x hq' hx]
  have h := slowEulerIntegral_contiguous (q + 1) m x hq' hx
  have hqq : q + 1 + 1 = q + 2 := by ring
  rw [hqq] at h
  have hg := Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (q + 1)
  rw [hqq] at hg
  linear_combination (Complex.Gamma (q + 1))⁻¹ * h -
    x * slowEulerIntegral (q + 2) (m + 2) x * hg

end DefocusingNLS
end OAI
