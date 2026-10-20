@[expose] public section

noncomputable section

namespace NavierStokes.AxisCoefficientSpace

open Set MeasureTheory

open scoped Topology BoundedContinuousFunction ContDiff

theorem hasDerivAt_jet_interior (I : Window) (w : ℕ → ℕ → ℝ)
    (A : CoefficientSpace I w) (n m : ℕ) {x : ℝ}
    (hx : x ∈ Ioo I.left I.right) :
    HasDerivAt (jet I w A.1 n m) (jet I w A.1 n (m + 1) x) x :=
  (hasDerivWithinAt_jet I w A n m ⟨hx.1.le, hx.2.le⟩).hasDerivAt
    (Icc_mem_nhds hx.1 hx.2)

end NavierStokes.AxisCoefficientSpace
end
end
