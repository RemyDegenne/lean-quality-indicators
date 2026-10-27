public section

open scoped TensorProduct

namespace TauCeti

namespace TensorWords

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

variable {G : InternalGrading R M} {q : ℤ}

variable {b : TensorWords R M →ₗ[R] TensorWords R M}

/-- The positive-arity Taylor correspondence for coaugmentation-preserving signed
coderivations. Its inverse is reduced Taylor expansion followed by extension by zero
on the empty word. -/
noncomputable def gradedCoderivEquivTaylor (G : InternalGrading R M) (q : ℤ) :
    coaugmentationPreservingGradedCoderivations G q ≃ₗ[R]
      (ReducedTensorWords R M →ₗ[R] M) where
  toFun b := ReducedTensorWords.letter R M ∘ₗ restrictReduced b.val
  invFun F := ⟨extendReduced (ReducedTensorWords.gradedCoderiv G F q),
    (mem_coaugmentationPreservingGradedCoderivations G q _).mpr
      ⟨isGradedCoderivation_extendReduced
        (ReducedTensorWords.isGradedCoderivation_gradedCoderiv G F q),
        extendReduced_one _⟩⟩
  left_inv b := by
    obtain ⟨hb, h₁⟩ := (mem_coaugmentationPreservingGradedCoderivations G q _).mp b.property
    exact Subtype.ext (hb.eq_extendReduced_gradedCoderiv h₁).symm
  right_inv F := by
    simp only [restrictReduced_extendReduced, ReducedTensorWords.letter_comp_gradedCoderiv]
  map_add' b c := by
    apply LinearMap.ext
    intro w
    simp
  map_smul' r b := by
    apply LinearMap.ext
    intro w
    simp

end TensorWords
end TauCeti
end
