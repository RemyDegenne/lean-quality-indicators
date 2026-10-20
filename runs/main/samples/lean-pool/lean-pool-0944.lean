@[expose] public section

noncomputable section

namespace NavierStokes.ActualMeanPhysicalData

open Set Function Filter ProblemStatement

open PhysicalResidualNaturality GaugeStateCoherence

open scoped Topology ContDiff BigOperators

open CorrectionInitialization.ActualPrimary

open CorrectionStep CorrectionState

section SourceClasses

variable {B N0 N : ℕ} {p : ℕ → CycleParameters (ActualInitialization.Index B N0)}
    (H : InitialCycleInput B N0 N p)

theorem cycleRank_class (j : ℕ) {α : ℝ}
    (HC : WeightedClasses.UnweightedClass ActualInitialMean.slowStrip α
      (CorrectionState.debt (commonContext B)
        ((p j).afterTemporal
          (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
              j).coefficients
          (commonContext B) (CycleState.iterate p (commonContext B)
              (ActualInitialization.initialCycleState B N0) j).state))) :
    WeightedClasses.MeanClass ActualInitialMean.strip α ((initialCycleData H).rankFamily j).native
        := by
  have hg : (p j).gauge = commonGauge := (H.realizes j).gauge.trans initialGeometry_gauge
  have hr : (p j).rank = rankData := (H.realizes j).rank.trans initialGeometry_rank
  have HG := ((initialCycleData H).stage_primitives j).rankGeometry
  rw [hg, hr] at HG
  have Hp := rankPotential_class (cL := FinalSlowBase.edgeExponent nominal / 4) (cR := 1)
    standardRegion commonGauge rankData (commonContext B) _
    (PrimaryTargetBounds.leftRadius_pos nominal)
    (div_pos (FinalSlowBase.edgeExponent_pos nominal) (by norm_num)) zero_lt_one
    (ChartScales.epsilon h) BaseContextAssembly.slowScale (ChartScales.epsilon_pos h)
    (ChartScales.epsilon_le_one h outgoing.data.h_pos.le) BaseContextAssembly.one_le_slowScale
    HG (rankData_parameters standardRegion.carrier) rankAmplitude_pos.ne'
    active_left_before_rank rank_before_active_right HC
  change WeightedClasses.MeanClass ActualInitialMean.strip α (VariableGaugeMean.rankPotential (p
      j).gauge (p j).rank _ _)
  rw [hg, hr]
  exact Hp

end SourceClasses
end NavierStokes.ActualMeanPhysicalData
end
end
