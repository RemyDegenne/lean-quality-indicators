namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Topology

open MeasureTheory Filter Set

open scoped Topology

open MeasureTheory ProbabilityTheory Filter Set

namespace SKFluctuations.Hierarchy

open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar

open scoped Topology NNReal BigOperators

section

variable (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0)
    {m : ℝ} (hm : 0 < m) (hmα : m ≤ α.mass l) (r : ℝ≥0)

theorem scalarClockProfileSlice_finite_prefix_root_pos (s : ℝ) (hs : 0 < s) (b : ℝ)
    (steps : List DensityStep)
    (hcenter : ∫ x in Ioi 0,
       (finiteTransformedResidual s hs b steps).rootWeight (scalarClockProfileSlice α hα l t hm hmα r)
         (scalarClockProfileJet α hα l t m r 0) x*
       (scalarClockProfileSlice α hα l t hm hmα r).Φ x = 0) :
    0 < ∫ x in Ioi 0,
       (finiteTransformedResidual s hs b steps).rootWeight (scalarClockProfileSlice α hα l t hm hmα r)
         (scalarClockProfileJet α hα l t m r 0) x*
       (scalarClockProfileSlice α hα l t hm hmα r).thirdTest x :=
  scalarClockProfileSlice_residual_root_pos α hα l t hm hmα r
    (finiteTransformedResidual_cone s hs b steps) hcenter

end
end SKFluctuations.Hierarchy
end
end OAI
