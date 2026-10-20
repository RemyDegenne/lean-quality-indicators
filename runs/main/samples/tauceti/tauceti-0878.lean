public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace TauCeti

namespace Probability

theorem spareStateProcess_identDistrib (n : ℕ) :
    IdentDistrib (spareStateProcess n) (spareStateProcess 0) spareStateMeasure
      spareStateMeasure :=
  ⟨(measurable_spareStateProcess n).aemeasurable,
    (measurable_spareStateProcess 0).aemeasurable, by
      rw [spareStateMeasure_map_spareStateProcess, spareStateMeasure_map_spareStateProcess]⟩

end Probability
end TauCeti
end
end
