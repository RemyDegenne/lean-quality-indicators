@[expose] public section

open TauCeti.DavisKahan.Sylvester

open scoped InnerProductSpace

namespace TauCeti

namespace DavisKahan1970

open TauCeti.DavisKahan

universe u v

section RealScalars

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
  [CompleteSpace H₁]

variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
  [CompleteSpace H₂]

variable (U₁ V₁ : Submodule ℝ H₁) [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection]

variable (U₂ V₂ : Submodule ℝ H₂) [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection]

theorem corollary3_1_prescribedAngleSequence_classification_real (θ : ℕ → ℝ)
    (hθ0 : ∀ n, 0 < θ n) (hθ2 : ∀ n, θ n < Real.pi / 2) (hanti : Antitone θ)
    (hlim : Filter.Tendsto θ Filter.atTop (nhds 0))
    (hcompact₂ : IsCompactOperator
      (U₂.starProjection ∘L
        (ContinuousLinearMap.id ℝ H₂ - V₂.starProjection) ∘L U₂.starProjection)) :
    PairOfSubspacesUnitaryEquivalent
        (sourceSubspace ℝ (AngleSequenceSpace ℝ) (AngleSequenceSpace ℝ))
        (angleSequenceDatum ℝ θ).targetSubspace U₂ V₂ ↔
      SameHalmosTrivialDimensions
        (sourceSubspace ℝ (AngleSequenceSpace ℝ) (AngleSequenceSpace ℝ))
        (angleSequenceDatum ℝ θ).targetSubspace U₂ V₂ ∧
      compactAngleEigenvalueList (genericCosineBlock U₂ V₂ᗮ) =
        fun n => Real.sin (θ n) ^ 2 := by
  rw [corollary3_1_compact_defectBlock_angleList_classification_real _ _ U₂ V₂
      (isCompactOperator_angleSequenceDefectBlock hlim) hcompact₂,
    compactAngleEigenvalueList_genericCosineBlock_angleSequenceDatum ℝ θ hθ0 hθ2 hanti]
  exact and_congr_right fun _ => eq_comm

end RealScalars
end DavisKahan1970
end TauCeti
end
