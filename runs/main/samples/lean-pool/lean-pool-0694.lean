@[expose] public section

noncomputable section

namespace NavierStokes.ActualCarrierGeometry

open Set Function Filter

open CorrectionInitialization ActualPrimary

open scoped Topology

section Windows

variable {B N0 : ℕ}

theorem nativeSlowCore_physicalBox (l : ActualPrimaryBounds.SignedLabel B N0)
    {p : Slow}
    (hp : p ∈ ActualGaussianCoverage.actualSlowCore certificate modulation
      (choice B N0).prepared l.2) :
    position l.2 p ∈ SlotColoring.physicalBox (CoordinateAlgebra.D h)
      (ActualPrimaryCovariance.signedLabelOf (l.2, l.1)) := by
  have hb := PrimaryRepresentatives.nativeMask_tsupport_subset l.2.val.property.1
    (PrimaryGeometryAssembly.label nominal l.2).2 hp
  intro j
  have ha : 0 < ChartScales.Q (BaseChartJets.cellBand l.2) ^
      SlotColoring.axisExponent (CoordinateAlgebra.D h) j :=
    Real.rpow_pos_of_pos (ChartScales.Q_pos _) _
  have hw := SlotColoring.width_pos (CoordinateAlgebra.D h) j l.2.val.property.1
  change 0 < SlotColoring.width (CoordinateAlgebra.D h) j (BaseChartJets.cellBand l.2) at hw
  change |position l.2 p j - SlotColoring.width (CoordinateAlgebra.D h) j
      (BaseChartJets.cellBand l.2) * ((PrimaryGeometryAssembly.label nominal l.2).2 j : ℝ)| ≤
    2 * SlotColoring.width (CoordinateAlgebra.D h) j (BaseChartJets.cellBand l.2)
  calc
    _ = (ChartScales.Q (BaseChartJets.cellBand l.2) ^
        SlotColoring.axisExponent (CoordinateAlgebra.D h) j) *
        |PrimaryRepresentatives.position p j - SquaredPartition.nativeSpacing
            (BaseChartJets.cellBand l.2) *
          ((PrimaryGeometryAssembly.label nominal l.2).2 j : ℝ)| := by
      rw [position_component, width_eq, mul_assoc, ← mul_sub, abs_mul, abs_of_pos ha]
    _ ≤ (ChartScales.Q (BaseChartJets.cellBand l.2) ^
        SlotColoring.axisExponent (CoordinateAlgebra.D h) j) *
        SquaredPartition.nativeSpacing (BaseChartJets.cellBand l.2) :=
      mul_le_mul_of_nonneg_left (by have hh := hb j; simp only [one_mul] at hh; exact hh) ha.le
    _ = SlotColoring.width (CoordinateAlgebra.D h) j (BaseChartJets.cellBand l.2) :=
      (width_eq _ _ _).symm
    _ ≤ _ := by linarith only [hw]

end Windows
end NavierStokes.ActualCarrierGeometry
end
end
