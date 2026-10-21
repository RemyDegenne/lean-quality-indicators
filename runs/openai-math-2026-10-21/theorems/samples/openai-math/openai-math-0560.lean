namespace OAI

noncomputable section

namespace PolycyclicRecognition

open Set MeasureTheory

open scoped ENNReal

theorem boundary_pullback_measure_apply
    {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    [MeasurableSpace S] [MeasurableSpace T] [BorelSpace S] [BorelSpace T]
    (B : S ≃ₜ T) (μ : Measure T) (E : Set S) :
    Measure.map B.symm μ E = μ (B '' E) := by
  rw [B.symm.measurableEmbedding.map_apply, B.preimage_symm]

end PolycyclicRecognition
end
end OAI
