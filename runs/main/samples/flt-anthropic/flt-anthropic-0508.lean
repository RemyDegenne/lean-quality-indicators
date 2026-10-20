namespace P2MW.S_AutomorphicForm_lintegral_enorm_twistedConj_mul_semiLocalHaar_eq_mul_lintegral_lintegral_torus_unipotentChart_of_isTwistedSectionFnOn_of_diagonal

attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain MeasureTheory Set Function

open scoped ENNReal NNReal TensorProduct TensorProduct.RightActions Pointwise

noncomputable section

namespace KcTwistedSplitUnfold

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => v.adicCompletion K

local notation "E" => L ⊗[K] v.adicCompletion K

local notation "Q" => (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K)

local notation "P" => Fin 4 → L ⊗[K] v.adicCompletion K

local notation "G" => GL (Fin 2) (L ⊗[K] v.adicCompletion K)

local notation "GF" => GL (Fin 2) (v.adicCompletion K)

attribute [local instance 9999] Algebra.toModule

attribute [local instance] isTopologicalRing_E t2Space_E locallyCompactSpace_E continuousSMul_E
  isScalarTower_FEE smulCommClass_FEE finite_KL

attribute [local instance] secondCountableTopology_E

theorem secondCountableTopology_GL : SecondCountableTopology G := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) E) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → E))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) E)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

end KcTwistedSplitUnfold
end
end P2MW.S_AutomorphicForm_lintegral_enorm_twistedConj_mul_semiLocalHaar_eq_mul_lintegral_lintegral_torus_unipotentChart_of_isTwistedSectionFnOn_of_diagonal
