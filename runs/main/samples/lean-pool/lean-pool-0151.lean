section

@[expose] public section

noncomputable section

open Set Filter Function MeasureTheory

open scoped Topology ContDiff BigOperators

namespace NavierStokes.EntranceAlignedBase

open GlobalSlowProfiles AssembledSlowBase

section Modulated

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    (H : NominalConeAssembly.Certificate W) {d : ModulatedProfileAssembly.LoopData W}
    (v : ModulatedProfileAssembly.Witness d)

theorem scales_weighted (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    ConstructedSlowBase.WeightedStressBound (scales H v c hc upper B) F.data.h
        (modulatedCoefficients H v)
      c (Real.log (NominalConeAssembly.activeLeft W)) (ConstructedSlowBase.activeRight W) := by
  apply modulated_weighted_on_actual_scales H v hc
    (SlowBorelBase.innerBox_isCompact 0 (ConstructedSlowBase.scaleUpper W upper)) _ (scales_spec H
        v c hc upper B).2
  intro p hp
  exact ⟨⟨(Real.exp_pos _).le.trans hp.1.1.le,
    hp.1.2.le.trans (le_max_right _ _)⟩, hp.2⟩

end Modulated
end NavierStokes.EntranceAlignedBase
end
end
end
