@[expose] public section

noncomputable section

namespace NavierStokes.ActualPrimaryCoherence

open Set Function Filter HarmonicCalculus

open scoped Topology ContDiff InnerProductSpace

open CorrectionInitialization

open CorrectionInitialization.ActualPrimary

variable {B N0 : ℕ}

theorem physicalPotential_smooth (j : Fin 2) (L : Label B N0) :
    ContDiffOn ℝ ∞ (physicalPotential j L) {z : ProblemStatement.SpaceTime | z.1 < 1 ∧ 0 < z.2 0}
        := by
  have he := PhysicalCurlCovariance.referencePotential_eq_on (ChartScales.Q_pos 0) h
      (CommonWindow.index h 0)
    liftedDomain_open one_ne_zero (chartCoefficients_frequency_pos j L 0).ne'
    (liftedPhase_smooth j L 0) (liftedAmplitude j L 0) (physicalPhase j L) (physicalAmplitude j L)
    (fun z hz => by simpa only [one_mul] using physicalPhase_eq j L 0 hz.1)
    (fun z hz => physicalAmplitude_eq j L 0 hz.1)
  intro z hz
  have hs := physical_source 0 hz.1 hz.2
  have hm := (PhysicalResidualBridge.commonGraph (ChartScales.Q 0) h (CommonWindow.index h
      0)).map_smoothAt
    (mul_pos (Real.rpow_pos_of_pos (ChartScales.Q_pos 0) _) hz.2).ne'
  have hc := ((liftedPotential_smooth j L 0).contDiffAt (liftedDomain_open.mem_nhds hs.2)).comp z hm
  apply ContDiffAt.contDiffWithinAt
  apply (hc.const_smul (ChartScales.Q 0 ^ (-h))).congr_of_eventuallyEq
  exact eventually_of_mem
    ((PhysicalResidualBridge.commonGraph (ChartScales.Q 0) h (CommonWindow.index h 0)).source_open
      (Real.rpow_pos_of_pos (ChartScales.Q_pos 0) _) liftedDomain_open |>.mem_nhds hs)
    (fun _ hy => he hy)

end NavierStokes.ActualPrimaryCoherence
end
end
