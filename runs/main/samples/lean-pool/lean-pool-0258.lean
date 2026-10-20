@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace Feige

noncomputable section

@[simp]
theorem augmentedTwoPointKernel_atom :
    augmentedTwoPointKernel (Sum.inl ()) = Measure.dirac 1 :=
  by simp [augmentedTwoPointKernel]

end
end Feige
end
