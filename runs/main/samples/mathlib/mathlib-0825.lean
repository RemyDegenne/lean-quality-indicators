@[expose] public section

open Real MeasureTheory Set

open scoped ENNReal NNReal

namespace InformationTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

lemma klDiv_ne_top (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) : klDiv μ ν ≠ ∞ :=
  klDiv_ne_top_iff.mpr ⟨hμν, h_int⟩

end InformationTheory
end
