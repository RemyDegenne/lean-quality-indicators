@[expose] public section

noncomputable section

open Set Function

open scoped NNReal Topology ENNReal

namespace MeasureTheory

namespace OuterMeasure

section sInfGen

variable {α : Type*}

theorem restrict_sInf_eq_sInf_restrict (m : Set (OuterMeasure α)) {s : Set α} (hm : m.Nonempty) :
    restrict s (sInf m) = sInf (restrict s '' m) := by
  simp only [sInf_eq_iInf, restrict_biInf, hm, iInf_image]

end sInfGen
end OuterMeasure
end MeasureTheory
end
end
