@[expose] public section

open MeasureTheory

open scoped ENNReal

namespace MeasureTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {μ ν : Measure 𝓧}

section ETVDist

lemma etvDist_triangle (μ ν ξ : Measure 𝓧) : etvDist μ ξ ≤ etvDist μ ν + etvDist ν ξ := by
  by_cases h : IsFiniteMeasure μ ∧ IsFiniteMeasure ν ∧ IsFiniteMeasure ξ
  · obtain ⟨_, _, _⟩ := h
    simp only [etvDist_eq_etvDist_toSignedMeasure]
    exact VectorMeasure.etvDist_triangle _ _ _
  simp only [not_and_or] at h
  rcases h with h | h | h <;>
    simp [etvDist_of_not_isFiniteMeasure_left h, etvDist_of_not_isFiniteMeasure_right h]

end ETVDist
end MeasureTheory
end
