namespace P2MW.S_AutomorphicForm_continuous_bruhatTransversal_tsum_of_re_gt_half

set_option Elab.async false

p2m_reactivate

p2m_reactivate

noncomputable section

p2m_open

open scoped Classical

namespace AutomorphicForm

namespace WeylIntegrable

p2m_open

p2m_reactivate

p2m_reactivate

section Generic2

variable {A : Type*} [CommRing A] {ε y z x : A}

def eUnit (h : SelRel ε y z x) : Aˣ := ⟨1 - 2 * ε, 1 - 2 * ε, one_sub_two_mul_sq h, one_sub_two_mul_sq h⟩

end Generic2
end WeylIntegrable
end AutomorphicForm
end
end P2MW.S_AutomorphicForm_continuous_bruhatTransversal_tsum_of_re_gt_half
