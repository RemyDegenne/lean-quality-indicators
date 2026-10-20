namespace P2MW.S_AutomorphicForm_exists_forall_prod_infinitePlace_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegralOn_tensorArch_scalar_mul

attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar

open IsDedekindDomain

open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped ENNReal

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

namespace B5w

open AutomorphicForm

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem val_scalar_mul {R : Type*} [CommRing R] (c : Rˣ) (g : GL (Fin 2) R) (i j : Fin 2) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) c * g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i j =
      (c : R) * (g : Matrix (Fin 2) (Fin 2) R) i j := by
  rw [Units.val_mul]
  have h : ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      Matrix.scalar (Fin 2) (c : R) := rfl
  rw [h, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, Matrix.smul_apply, smul_eq_mul]

end B5w
end P2MW.S_AutomorphicForm_exists_forall_prod_infinitePlace_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegralOn_tensorArch_scalar_mul
