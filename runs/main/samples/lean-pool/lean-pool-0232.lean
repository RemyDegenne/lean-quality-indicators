@[expose] public noncomputable section

open scoped ContDiff MatrixOrder Topology

open scoped Convolution

open scoped ENNReal

open ContinuousLinearMap MeasureTheory

namespace ViscositySolns

variable {n : Nat}

theorem SmoothConvexApproximationOnInteriorClosedBallTheorem.of_extensionMollification
    (hmoll : ContinuousExtensionConvexMollificationOnInteriorClosedBallTheorem n) :
    SmoothConvexApproximationOnInteriorClosedBallTheorem n := by
  intro g x0 R r hr hrR hconv
  rcases exists_continuous_extension_eqOn_intermediate_closedBall_of_convexOn_closedBall
      (n := n) (g := g) (x0 := x0) (R := R) (r := r) hr hrR hconv with
    ⟨Rmid, hrRmid, hRmidR, G, hGcont, hGeq⟩
  have hconv_mid : ConvexOn Real (Metric.closedBall x0 Rmid) g :=
    hconv.subset
      (Metric.closedBall_subset_closedBall (le_of_lt hRmidR))
      (convex_closedBall x0 Rmid)
  exact hmoll g G x0 Rmid r hr hrRmid hconv_mid hGcont hGeq

end ViscositySolns
end
