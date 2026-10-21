namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]

theorem jointBooleanSampler_image_law (h : D → ℕ) (c : ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α) :
    Measure.map (jointBooleanSampler h c sets) (jointBooleanSource h) =
      sigmaAxisMeasure (fun d => Measure.map (booleanSamplerMap (F := Fin (h d)) (c d) (sets d))
        (blockCubeMeasure (B d) (Fin (h d)) α)) :=
  sigmaAxisSampler_image_law _ _ (fun d => (booleanSamplerMap_contDiff (c d) (sets d)).continuous.measurable)

end Erdos3
end
end OAI
