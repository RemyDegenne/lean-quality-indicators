namespace P2MW.S_AutomorphicForm_GL2Real_eq_neg_eight_mul_pi_of_forall_tendsto_ellipticTransform_entrySlice

set_option autoImplicit false

open MeasureTheory Set Filter

noncomputable section

namespace AutomorphicForm

namespace GL2Real

namespace RHead

p2m_open

open AutomorphicForm.GL2Real.RCoord AutomorphicForm.GL2Real.RLim

theorem dθMm_identity (r θ : ℝ) (q : ℝ × ℝ) (hq : q.1 ≠ 0) (hsv : Real.sin θ ^ 2 + q.2 ^ 2 ≠ 0) :
    (q.1)⁻¹ • dθMm r θ q =
      (-(r * Real.sin θ / q.1)) • eI +
        (-(2 * Real.sin θ * Real.cos θ / (Real.sin θ ^ 2 + q.2 ^ 2))) • (duMm r θ q + (-r) • e10) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dθMm, duMm, eI, e01, e10] <;> field_simp <;> ring

end RHead
end GL2Real
end AutomorphicForm
end
end P2MW.S_AutomorphicForm_GL2Real_eq_neg_eight_mul_pi_of_forall_tendsto_ellipticTransform_entrySlice
