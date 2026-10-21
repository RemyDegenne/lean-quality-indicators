namespace OAI

noncomputable section

section

open MeasureTheory Set

open scoped ContDiff

open Filter Set

open scoped Topology

open Set MeasureTheory Filter

open scoped Topology ContDiff

namespace RVM

lemma differenceEnergy_nonneg (s₁ s₂ : Solution) (p : ℝ × Vec) :
    0 ≤ differenceEnergy s₁ s₂ p := by
  apply add_nonneg (differenceFieldEnergy_nonneg _ _ _)
  rw [particleMoment_one]
  exact integral_nonneg (fun v => squareDifference_nonneg _ _ _)

end RVM
end
end
end OAI
