public section

open scoped MeasureTheory NNReal ENNReal

variable {α β : Type*} {m : MeasurableSpace α}

namespace MeasureTheory

namespace Measure

variable {μ ν : Measure α}

section integral

lemma integral_toReal_rnDeriv [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    ∫ x, (μ.rnDeriv ν x).toReal ∂ν = μ.real Set.univ := by
  rw [← setIntegral_univ, setIntegral_toReal_rnDeriv hμν Set.univ]

end integral
end Measure
end MeasureTheory
end
