namespace OAI

noncomputable section

namespace KadisonSimilarity

open MeasureTheory

variable {A H : Type*} [CommCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (D : CyclicDecompositionData π.range)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

theorem commonFieldCompression_mem
    (R : WeakDual.characterSpace ℂ A → ScalarHilbertCoordinates D.generators →L[ℂ]
      ScalarHilbertCoordinates D.generators)
    (hmeas : ∀ v, AEStronglyMeasurable (fun x => R x v) (cyclicCommonBaseMeasure π D))
    (C : ℝ) (hbound : ∀ᵐ x ∂cyclicCommonBaseMeasure π D, ‖R x‖ ≤ C) :
    commonFieldCompression π D R hmeas C hbound ∈ starSubalgebraCommutant π.range := by
  rw [← SetLike.mem_coe, coe_starSubalgebraCommutant]
  rintro _ ⟨a, rfl⟩
  apply Eq.symm
  apply commonCompression_commutes_representation π D
  intro b
  rw [commonScalarRepresentation_apply]
  exact boundedFieldOperator_commutes_continuous (cyclicCommonBaseMeasure π D)
    R hmeas C hbound (gelfandStarTransform A b)

end KadisonSimilarity
end
end OAI
