set_option warningAsError true

@[expose] public section

noncomputable section

universe uN uE uQ uH

namespace ContinuousGroupExtension

variable {N : Type uN} {E : Type uE} {Q : Type uQ}
  [Group N] [Group E] [Group Q]
  [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q]
  [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q]

/-- The value of the quotient action at any element, bundled as a continuous
automorphism of topological abelianization. -/
def quotientConjActTopologicalAbelianizationContinuous
    (S : ContinuousGroupExtension N E Q) (q : Q) :
    TopologicalAbelianization N ≃ₜ* TopologicalAbelianization N where
  toMulEquiv := S.quotientConjActTopologicalAbelianization q
  continuous_toFun := by
    obtain ⟨e, rfl⟩ := S.rightHom_surjective q
    rw [S.quotientConjActTopologicalAbelianization_rightHom]
    exact (S.conjActTopologicalAbelianizationContinuous e).continuous
  continuous_invFun := by
    obtain ⟨e, rfl⟩ := S.rightHom_surjective q
    rw [S.quotientConjActTopologicalAbelianization_rightHom]
    exact (S.conjActTopologicalAbelianizationContinuous e).symm.continuous

end ContinuousGroupExtension
end
end
