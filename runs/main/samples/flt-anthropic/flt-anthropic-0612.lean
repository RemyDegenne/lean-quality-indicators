namespace P2MW.S_AutomorphicForm_finiteDimensional_iInf_iSup_typeSubmodule_mulSingle

set_option autoImplicit false

noncomputable section

namespace KcFinDim

open AutomorphicForm

section Main

variable {Pl : Type*} [Fintype Pl] [DecidableEq Pl] {K : Pl → Type*} [∀ w, Group (K w)]
  {ι : Pl → Type*} [∀ w, Fintype (ι w)]
  {W : ∀ w, ι w → Type*} [∀ w i, AddCommGroup (W w i)] [∀ w i, Module ℂ (W w i)]
  [∀ w i, FiniteDimensional ℂ (W w i)]
  (ρ : ∀ w i, Representation ℂ (K w) (W w i))

theorem restrictTo_univ (κ : Gp K) : restrictTo Finset.univ κ = κ := by
  funext w
  simp [restrictTo]

end Main
end KcFinDim
end
end P2MW.S_AutomorphicForm_finiteDimensional_iInf_iSup_typeSubmodule_mulSingle
