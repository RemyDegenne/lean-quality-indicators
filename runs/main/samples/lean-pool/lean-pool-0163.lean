@[expose] public section

noncomputable section PortComputability

open MeasureTheory ProbabilityTheory Set

namespace MarkovProcess

section

namespace Kernel

variable {β alpha : Type*} [MeasurableSpace β] [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [T2Space alpha]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]

theorem IsSupportedOnContinuousPaths.map_denseRestriction
    (κ : Kernel β (DenseTime → alpha)) (hκ : IsSupportedOnContinuousPaths κ)
    (default : ContinuousPath alpha) :
    (toContinuousPathKernel κ default).map ContinuousPath.denseRestriction = κ := by
  rw [toContinuousPathKernel_eq_map, ← Kernel.map_comp_right]
  · ext x s hs
    rw [Kernel.map_apply' _
      ((ContinuousPath.measurable_denseRestriction).comp
        (ContinuousPath.measurable_continuousExtension default)) x hs]
    have hfun :
        ContinuousPath.denseRestriction ∘ ContinuousPath.continuousExtension default
          =ᵐ[κ x] id :=
      (hκ x).mono fun path hpath ↦
        ContinuousPath.denseRestriction_continuousExtension_of_mem_range default hpath
    simpa only [Set.preimage_id] using measure_congr (hfun.preimage s)
  · exact ContinuousPath.measurable_continuousExtension default
  · exact ContinuousPath.measurable_denseRestriction

end Kernel
end
end MarkovProcess
end PortComputability
end
