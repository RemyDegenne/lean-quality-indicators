@[expose] public section

open scoped TensorProduct

namespace BGS.HasseWeil

noncomputable section

variable (C L N S : Type*) [Field C] [Field L] [Field N] [Field S]
  [Algebra C L] [Algebra L N] [Algebra C N] [IsScalarTower C L N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]
  [FiniteDimensional L N] [IsGalois L N]

section FiniteConstants

variable [Fintype C] [Finite S]

omit [IsGalois L N] [Finite S] in
theorem isGalois_exactConstantExtension_over_frobeniusTwistField
    (hExact : algebraicClosure C N = (⊥ : IntermediateField C N))
    (g : N ≃ₐ[L] N) :
    letI := exactConstantExtensionField C N S hExact
    letI := exactConstantExtensionBaseAlgebra C L N S
    IsGalois
      (exactConstantExtensionFrobeniusTwistField C L N S hExact g)
      (ExactConstantExtension C N S) := by
  let := exactConstantExtensionField C N S hExact
  let := exactConstantExtensionBaseAlgebra C L N S
  let : FiniteDimensional L (ExactConstantExtension C N S) :=
    finiteDimensional_exactConstantExtension_over_base C L N S hExact
  let H := exactConstantExtensionFrobeniusTwistSubgroup C L N S g
  change IsGalois (IntermediateField.fixedField H)
    (ExactConstantExtension C N S)
  exact IsGalois.of_fixed_field (ExactConstantExtension C N S) H

end FiniteConstants
end
end BGS.HasseWeil
end
