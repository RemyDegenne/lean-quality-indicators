namespace P2MW.S_NumberField_TateGlobal_exists_forall_exists_isIdeleClassChar_isUnramifiedCharAt_archLocalChar_eq_abs_sub_le

attribute [-instance] instCountableOfNumberField_definitions

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open IsDedekindDomain NumberField

open NumberField.AdelicLevel NumberField.AdelicVolume AutomorphicForm NumberField.TateGlobal

open NumberField.InfinitePlace NumberField.mixedEmbedding NumberField.Units NumberField.Units.dirichletUnitTheorem

open scoped Classical

namespace R4TwistNormExist

section Arch

variable (F : Type) [Field F] [NumberField F]

variable {F}

variable (F) in

noncomputable def logAll (x : mixedSpace F) : InfinitePlace F → ℝ :=
  fun w => (mult w : ℝ) * Real.log ‖evalC F w x‖

end Arch
end R4TwistNormExist
end P2MW.S_NumberField_TateGlobal_exists_forall_exists_isIdeleClassChar_isUnramifiedCharAt_archLocalChar_eq_abs_sub_le
