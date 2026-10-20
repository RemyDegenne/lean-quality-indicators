@[expose] public section

noncomputable section

namespace NavierStokes.PrimaryRepresentatives

open Set Function Filter

open scoped ContDiff Topology InnerProductSpace

/-- `T` is a continuous target direction, including at zero-amplitude edges. -/
structure TargetCone (F : ℝ) (g T : Plane) : Prop where
  inward : ⟪T, normalDirection g⟫_ℝ < 0
  ratio_lt_one : targetRatio F g T < 1

end NavierStokes.PrimaryRepresentatives
end
end
