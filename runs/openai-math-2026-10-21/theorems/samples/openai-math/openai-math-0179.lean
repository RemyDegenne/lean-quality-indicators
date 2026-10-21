namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set

open scoped ENNReal NNReal

variable {X : Type*} [MeasurableSpace X]

theorem cellHaar_zero_of_notMem (μ : Measure X) (A B : Set X) (hAB : A ⊆ B)
    (x : X) (hx : x ∉ B) : cellHaar μ A B x = 0 := by
  rw [cellHaar, normalizedSetIndicator_of_notMem μ A x (fun h => hx (hAB h)),
    normalizedSetIndicator_of_notMem μ B x hx, sub_self, mul_zero]

end
end RieszRectifiability
end OAI
