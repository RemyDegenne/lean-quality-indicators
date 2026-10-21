namespace OAI

universe uAlpha uBeta

noncomputable section

open MeasureTheory Set

namespace Problem356

namespace LocalBranchMeasure

variable {α : Type uAlpha} {β : Type uBeta} [TopologicalSpace α] [TopologicalSpace β]
  [MeasurableSpace α] [MeasurableSpace β] [BorelSpace α] [BorelSpace β]

omit [BorelSpace α] [BorelSpace β] in
theorem map_extendedBranch (e : OpenPartialHomeomorph α β) (z : β)
    (ν : Measure α) (hν : ∀ᵐ x ∂ν, x ∈ e.source) :
    Measure.map (extendedBranch e z) ν = Measure.map e ν := by
  apply Measure.map_congr
  filter_upwards [hν] with x hx
  exact extendedBranch_apply_of_mem e z hx

end LocalBranchMeasure
end Problem356
end
end OAI
