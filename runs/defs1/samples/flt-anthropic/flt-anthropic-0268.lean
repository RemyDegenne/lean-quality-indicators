namespace P2MW.S_AutomorphicForm_GL2Real_eq_neg_eight_mul_pi_of_forall_tendsto_ellipticTransform_entrySlice

set_option autoImplicit false

open MeasureTheory Set Filter

noncomputable section

namespace AutomorphicForm

namespace GL2Real

namespace RHead

p2m_open

open AutomorphicForm.GL2Real.RCoord AutomorphicForm.GL2Real.RLim

section IBP

variable {ψ : E22 → ℂ}

def Jint (ψ : E22 → ℂ) (r θ : ℝ) (q : ℝ × ℝ) : ℂ :=
  (((Real.sin θ ^ 2 + q.2 ^ 2)⁻¹ : ℝ) : ℂ) *
    (fderiv ℝ ψ (Matrix.of.symm (Mp r θ q)) e10 - fderiv ℝ ψ (Matrix.of.symm (Mm r θ q)) e10)

end IBP
end RHead
end GL2Real
end AutomorphicForm
end
end P2MW.S_AutomorphicForm_GL2Real_eq_neg_eight_mul_pi_of_forall_tendsto_ellipticTransform_entrySlice
