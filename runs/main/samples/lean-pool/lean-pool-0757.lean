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

omit [IsGalois L N] in
theorem natCard_aut_exactConstantExtension_over_frobeniusTwistField
    (hExact : algebraicClosure C N = (⊥ : IntermediateField C N))
    (g : N ≃ₐ[L] N)
    (hdiv : Nat.card (N ≃ₐ[L] N) ∣ Module.finrank C S) :
    letI := exactConstantExtensionField C N S hExact
    letI := exactConstantExtensionBaseAlgebra C L N S
    Nat.card
        (ExactConstantExtension C N S ≃ₐ[
          exactConstantExtensionFrobeniusTwistField C L N S hExact g]
          ExactConstantExtension C N S) = Module.finrank C S := by
  let := exactConstantExtensionField C N S hExact
  let := exactConstantExtensionBaseAlgebra C L N S
  let : FiniteDimensional L (ExactConstantExtension C N S) :=
    finiteDimensional_exactConstantExtension_over_base C L N S hExact
  let : IsGalois
      (exactConstantExtensionFrobeniusTwistField C L N S hExact g)
      (ExactConstantExtension C N S) :=
    isGalois_exactConstantExtension_over_frobeniusTwistField
      C L N S hExact g
  rw [IsGalois.card_aut_eq_finrank,
    finrank_exactConstantExtension_over_frobeniusTwistField
      C L N S hExact g hdiv]

end FiniteConstants
end
end BGS.HasseWeil
end
