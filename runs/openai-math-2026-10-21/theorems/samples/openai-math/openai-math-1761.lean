namespace OAI

noncomputable section

namespace SharpLiebThirring.OperatorProof

open MeasureTheory Set

open scoped Topology ENNReal

theorem sharp_lieb_thirring_spectral {γ : ℝ} (hγ₀ : 1/2 < γ) (hγ₁ : γ < 3/2) :
    (∀ (W : ℝ → ℝ) (hW : Admissible γ W),
      spectralMoment hγ₀ hW ≤ ENNReal.ofReal (sharpConstant γ)*potentialMass γ W) ∧
    spectralOptimalConstant hγ₀ = ENNReal.ofReal (sharpConstant γ) ∧
    spectralOneStateConstant hγ₀ = ENNReal.ofReal (sharpConstant γ) ∧
    ∃ hW : Admissible γ (equalityPotential γ),
      0 < potentialMass γ (equalityPotential γ) ∧
      spectralMoment hγ₀ hW = ENNReal.ofReal (sharpConstant γ)*potentialMass γ (equalityPotential γ) := by
  obtain ⟨hb,ho,hs,hW,hp,he⟩ := sharp_lieb_thirring γ hγ₀ hγ₁
  refine ⟨fun W hW ↦ ?_,?_,?_,hW,hp,?_⟩
  · rw [spectralMoment_eq hγ₀ hγ₁ hW]
    exact hb W hW
  · rw [spectralOptimalConstant_eq hγ₀ hγ₁]; exact ho
  · rw [spectralOneStateConstant_eq hγ₀]; exact hs
  · rw [spectralMoment_eq hγ₀ hγ₁ hW]; exact he

end SharpLiebThirring.OperatorProof
end
end OAI
