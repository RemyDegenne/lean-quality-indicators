@[expose] public section

noncomputable section

namespace NavierStokes.PrimaryRepresentatives

open Set Function Filter

open scoped ContDiff Topology InnerProductSpace

theorem physicalBox_normalizes (D : ℝ) (L : SlotColoring.Label) {x : Position}
    (hx : x ∈ SlotColoring.physicalBox D L) :
    normalizedSlow D L.1 x ∈ gridBox L.1 L.2.1 2 := by
  intro j
  have hp : 0 < ChartScales.Q L.1 ^ SlotColoring.axisExponent D j :=
    Real.rpow_pos_of_pos (ChartScales.Q_pos _) _
  have he : position (normalizedSlow D L.1 x) j -
      SquaredPartition.nativeSpacing L.1 * (L.2.1 j : ℝ) =
      (x j - SlotColoring.width D j L.1 * (L.2.1 j : ℝ)) /
        (ChartScales.Q L.1 ^ SlotColoring.axisExponent D j) := by
    simp only [normalizedSlow, position_slow, SquaredPartition.slowCoordinates,
      width_eq_scaled_spacing]
    field_simp
  rw [he, abs_div, abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  have hj := hx j
  rw [width_eq_scaled_spacing] at hj
  rw [width_eq_scaled_spacing]
  nlinarith only [hj]

end NavierStokes.PrimaryRepresentatives
end
end
