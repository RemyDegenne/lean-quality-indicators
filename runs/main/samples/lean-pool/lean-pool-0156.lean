@[expose] public section

local macro_rules | `($x ^ $n:num) => `($x ^ ($n : ℕ))

noncomputable section

open Set Filter MeasureTheory

open scoped Topology ContDiff

open NavierStokes.OutgoingSchedule NavierStokes.OutgoingTail

namespace NavierStokes.TailEnergyBounds

theorem postPulseEnergy_contDiff (d : TailData) : ContDiff ℝ ∞ (postPulseEnergy d) := by
  have hi := ParametricRephase.intervalIntegral_contDiffOn_of_joint
    (fun p : ℝ × ℝ => energyDensity d p.1 p.2) univ isOpen_univ
    (energyDensity_contDiff d).contDiffOn d.core.endpoint d.flattenEnd (flattenEnd_gt_core d).le
  have hi' : ContDiff ℝ ∞ (fun eta => ∫ y in d.core.endpoint..d.flattenEnd, energyDensity d eta y)
      :=
    contDiffOn_univ.mp hi
  have heq : postPulseEnergy d = (fun eta =>
      (∫ y in d.core.endpoint..d.flattenEnd, energyDensity d eta y) +
        ∫ y in Ioi d.flattenEnd, energyDensity d 0 y) :=
    funext (postPulseEnergy_split_flattenEnd d)
  rw [heq]
  exact hi'.add contDiff_const

end NavierStokes.TailEnergyBounds
end
end
