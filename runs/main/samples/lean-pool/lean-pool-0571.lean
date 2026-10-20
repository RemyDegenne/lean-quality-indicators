@[expose] public section

noncomputable section

namespace NavierStokes.ActualSignedGeometry

open Set Function Filter WeightedClasses PhaseJetBounds PrimaryCopyBounds

open scoped ContDiff Topology BigOperators

section ReferenceViews

variable {D h : ℝ} {vr vt : Plane}
  (sys : PartitionedCovariance.SlotSystem D h vr vt)
  (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)

theorem slotGeometry_refine (l : SlotColoring.Label) (gap : ℕ) :
    CopySolveCompatibility.refineGeometry (slotGeometry sys hdet l 0) gap =
      slotGeometry sys hdet l gap := by
  simp only [CopySolveCompatibility.refineGeometry, slotGeometry, CommonCoverClass.bandGeometry,
      zero_add]

end ReferenceViews
end NavierStokes.ActualSignedGeometry
end
end
