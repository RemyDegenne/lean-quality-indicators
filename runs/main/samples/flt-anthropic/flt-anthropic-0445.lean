namespace P2MW.S_AutomorphicForm_exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd

attribute [-instance] instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open NumberField IsDedekindDomain

open scoped TensorProduct Polynomial

open scoped TensorProduct.RightActions

namespace InertProof

open AutomorphicForm

theorem Matrix.irreducible_charpoly_of_not_isSquare_trace_sq_sub_four_mul_det
    (F : Type) [Field F] (γ : Matrix (Fin 2) (Fin 2) F)
    (hγ : ¬ IsSquare (Matrix.trace γ ^ 2 - 4 * Matrix.det γ)) :
    Irreducible (Matrix.charpoly γ) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    decide
  · intro r hr
    apply hγ
    refine ⟨2 * r - Matrix.trace γ, ?_⟩
    rw [Matrix.charpoly_fin_two] at hr
    simp only [Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C] at hr
    linear_combination (-4 : F) * hr

end InertProof
end P2MW.S_AutomorphicForm_exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd
