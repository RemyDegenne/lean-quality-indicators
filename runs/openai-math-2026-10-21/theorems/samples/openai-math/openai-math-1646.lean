namespace OAI

namespace CompanionFPP

open MeasureTheory ProbabilityTheory Real Finset

open scoped ENNReal

theorem finitePassageTime_cgf_recursion (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) (a : ℝ) (ha : |a| ≤ 1/2)
    (hq : 4*a^2*R ≤ 1/2) :
    cgf (finitePassageTime x y R) (Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)) a ≤
      2*cgf (finitePassageTime x y R) (Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)) (a/2)
        + 8*a^2*R := by
  let P := Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)
  let F := finitePassageTime x y R
  have hM : 0 < mgf F P a := mgf_pos (integrable_finitePassageTime_exp x y R hR a
    ((le_abs_self a).trans ha))
  have hM2 : 0 < mgf F P (a/2) := mgf_pos (integrable_finitePassageTime_exp x y R hR (a/2)
    (by have := (le_abs_self a).trans ha; linarith))
  have hrec := finitePassageTime_mgf_recursion x y R hR a ha
  have hden : 0 < 1-4*a^2*R := by linarith
  have hr : mgf F P a ≤ (mgf F P (a/2))^2/(1-4*a^2*R) := by
    apply (le_div_iff₀ hden).mpr
    change mgf F P a ≤ (mgf F P (a/2))^2 + (4*a^2*R)*mgf F P a at hrec
    nlinarith
  have hl := log_le_log hM hr
  rw [log_div (pow_ne_zero _ hM2.ne') hden.ne', log_pow] at hl
  have hlog := neg_log_one_sub_le (4*a^2*R) (by positivity) hq
  change log (mgf F P a) ≤ 2*log (mgf F P (a/2)) + 8*a^2*R
  norm_num only [Nat.cast_ofNat] at hl
  linarith

end CompanionFPP
end OAI
