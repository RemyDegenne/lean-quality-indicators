namespace P2MW.S_AutomorphicForm_finiteDimensional_iInf_iSup_typeSubmodule_mulSingle

set_option autoImplicit false

noncomputable section

namespace KcFinDim

open AutomorphicForm

section SpanTranslates

variable {H G : Type*} [Group H] [Group G]

theorem rt_mul (x₀ x₁ : G) (v : G → ℂ) : rt (x₀ * x₁) v = rt x₀ (rt x₁ v) := by
  funext x
  simp only [rt_apply, mul_assoc]

end SpanTranslates
end KcFinDim
end
end P2MW.S_AutomorphicForm_finiteDimensional_iInf_iSup_typeSubmodule_mulSingle
