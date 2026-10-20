namespace P2MW.S_AutomorphicForm_LocalFunctionSpace_eq_zero_of_forall_apply_diagOne_eq_zero_of_irreducible_of_admissible

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option linter.style.longFile 0

noncomputable section

open IsDedekindDomain NumberField

open scoped WithZero Pointwise

namespace KirillovInjectivity

variable {p : HeightOneSpectrum (𝓞 ℚ)}

local notation "F" => HeightOneSpectrum.adicCompletion ℚ p

local notation "Mat" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)

local notation "G" => GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)

local notation "ψ" => NumberField.StandardAddChar.psiV p

theorem psi_eq_one_of_mem_ball_zero {x : F} (hx : x ∈ ball p 0) : ψ x = 1 :=
  psi_eq_one_of_v_le_one (by simpa [mem_ball] using hx)

end KirillovInjectivity
end
end P2MW.S_AutomorphicForm_LocalFunctionSpace_eq_zero_of_forall_apply_diagOne_eq_zero_of_irreducible_of_admissible
