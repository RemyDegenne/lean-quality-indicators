public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace TauCeti.Probability

variable {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]

theorem measurable_arrayRowCoding :
    Measurable fun q : ProbabilityMeasure (ℕ → α) × (ℕ → unitInterval) ↦
      (q.1, fun p : ℕ × ℕ ↦ unitIntervalCoding (ℕ → α) q.1 (q.2 p.1) p.2) :=
  measurable_fst.prodMk (Measurable.of_eval fun p ↦ measurable_unitIntervalCoding_entry p)

end TauCeti.Probability
end
end
