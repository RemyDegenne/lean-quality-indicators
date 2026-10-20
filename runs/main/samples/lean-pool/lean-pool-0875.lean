@[expose] public section

local macro_rules | `($x ^ $n:num) => `($x ^ ($n : ℕ))

noncomputable section

namespace NavierStokes.OutgoingEntranceCone

open Set Filter MeasureTheory

open scoped Topology ContDiff

open OutgoingSchedule OutgoingTail NaturalAxisData

theorem normalizedEnergyHistory_hasDerivAt_eta (c : Parameters) (y η : ℝ) :
    HasDerivAt (normalizedEnergyHistory c y)
      (2 * η * averagedDropSquare c y + shapeGradient η * averagedEnergy c y η) η := by
  convert! (((hasDerivAt_id η).pow 2).mul_const (averagedDropSquare c y)).sub
    ((averagedEnergy_hasDerivAt_eta c y η).const_mul (1 / 2)) using 1
  simp only [id_eq]
  ring

end NavierStokes.OutgoingEntranceCone
end
end
