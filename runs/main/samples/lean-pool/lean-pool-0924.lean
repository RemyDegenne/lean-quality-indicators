@[expose] public section

noncomputable section

namespace NavierStokes.ActualPhaseDefect

open Set Function Filter HarmonicCalculus

open scoped ContDiff Topology BigOperators

section Actual

open CorrectionInitialization CorrectionInitialization.ActualPrimary

variable {B N0 : ℕ}

theorem chart_material_view (j : Fin 2) (L : Label B N0) (n : ℕ)
    (hi : CommonWindow.index h n ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand L))
    {x : FullPoint} (hT : 0 < x.1.2.1.1) (hR : 0 < x.1.1)
    (hp : ((viewMap L n x).1.1, (viewMap L n x).1.2.1) ∈
      (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).carrier L) :
    defect j L n x =
      (((ChartScales.carrier h (BaseChartJets.cellBand L):ℝ)/(ChartScales.carrier h n:ℝ)) *
        PhysicalParticularWave.clockWeight h (ChartScales.Q n) (ChartScales.Q
            (BaseChartJets.cellBand L))) *
      referenceMaterial j L (viewMap L n x) := by
  have hphys := CommonBaseContext.context_matches_physical certificate modulation upper B
    (CommonWindow.index h) n
  have hswap := context_material_swap (commonContext B)
    (BaseContextAssembly.nativeStrip nominal standardRegion) (chartCoefficients j L) n
    (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n))
    hphys rfl
    (ActualSignedGeometry.preparedViewPhase certificate modulation slots (choice B N0).prepared
      j L n (CommonWindow.index h n))
    (funext (chartCoefficients_phase_view j L n hi)) x
  apply hswap.trans
  have hF := ((phases B N0 j).baseF.smooth L).contDiffAt
    (((PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).isOpen L).mem_nhds hp)
  have hG := ((phases B N0 j).baseG.smooth L).contDiffAt
    (((PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).isOpen L).mem_nhds hp)
  have hPhi := ActualSignedGeometry.periodicPhase_differentiableAt slots
    (PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label nominal L) j) 0
    (ChartScales.epsilon h (BaseChartJets.cellBand L))
    ((phases B N0 j).phase.p L) ((phases B N0 j).phase.pz L) ((phases B N0 j).phase.x0 L)
    ((phases B N0 j).phase.F L) ((phases B N0 j).phase.G L)
    (hF.differentiableAt (by simp)) (hG.differentiableAt (by simp))
  have he := material_chartChange (ChartScales.Q_pos n) (ChartScales.Q_pos (BaseChartJets.cellBand
      L))
    h (CommonWindow.index h n) (ChartScales.nativeIndex h (BaseChartJets.cellBand
        L)-CommonWindow.index h n)
    ((ChartScales.carrier h (BaseChartJets.cellBand L):ℝ)/(ChartScales.carrier h n:ℝ))
    (fun y => (chartCoefficients j L).radialBase n (PhysicalResidualTZ.swapCylinder y))
    (fun y => (chartCoefficients j L).frequencyBase n (PhysicalResidualTZ.swapCylinder y))
    (fun y => (chartCoefficients j L).axialBase n (PhysicalResidualTZ.swapCylinder y))
    (fun y => BaseContextAssembly.radialSlow certificate modulation upper B (BaseChartJets.cellBand
        L)
      (y.1.1,y.1.2.1))
    (fun y => (phases B N0 j).phase.F L (y.1.1,y.1.2.1))
    (fun y => (phases B N0 j).phase.G L (y.1.1,y.1.2.1)) _
    (x := PhysicalResidualTZ.swapCylinder x) hR hPhi
    (radialSlow_change certificate modulation upper B n (BaseChartJets.cellBand L)
      (BaseContextAssembly.slowCoordinates x.1))
    (frequencySlow_change certificate modulation upper B n (BaseChartJets.cellBand L) hT hR)
    (axialSlow_change certificate modulation upper B n (BaseChartJets.cellBand L) hT)
  simp only [Nat.add_sub_of_le hi] at he
  exact he

end Actual
end NavierStokes.ActualPhaseDefect
end
end
