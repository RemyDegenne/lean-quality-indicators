namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

open scoped NNReal ENNReal

namespace Problem367

local instance finiteIsingBrownianEntropyNonemptySpin : Nonempty IsingSpin := ⟨.neg⟩

theorem finiteIsingBrownianEntropy_nonneg {d : ℕ} {Ω : Type*}
    (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ)
    (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) :
    0 ≤ finiteIsingBrownianEntropy beta D v B t p := by
  exact FinitePosterior.fieldEntropy_nonneg _ _ _ _
    (fun eta => by cases eta v <;> simp [spinSign])
    ⟨fun _ => .neg, rfl⟩ ⟨fun _ => .pos, rfl⟩

end Problem367
end
end OAI
