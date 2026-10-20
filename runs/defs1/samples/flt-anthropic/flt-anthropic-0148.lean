namespace P2MW.S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half

set_option Elab.async false

p2m_reactivate

p2m_reactivate

noncomputable section

p2m_open

open scoped Classical

namespace AutomorphicForm

namespace WeylIntegrable

p2m_open

section Generic

variable {A : Type*} [CommRing A] {ε y z x : A}

def mInvMat (ε z x : A) : Matrix (Fin 2) (Fin 2) A :=
  !![(2 * ε - 1) * ((1 - ε) * x + ε), -((2 * ε - 1) * (1 - ε)); -((2 * ε - 1) * (1 - ε + ε * z)), (2 * ε - 1) * ε]

end Generic
end WeylIntegrable
end AutomorphicForm
end
end P2MW.S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half
