@[expose] public section

noncomputable section

namespace EulerCylinderSmoothOrbit

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerMetricTransport EulerTransportDerivatives EulerLiftedWeakDerivative

open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [Fact (0 < P)] in
theorem coverField_fderiv (f : LiftDomain P → V) (z : LiftTangent) :
    fderiv ℝ (fun y : LiftTangent => f (y.1,(y.2 : AddCircle P))) z =
      fieldFDeriv P f (z.1,(z.2 : AddCircle P)) := by
  rw [coverField_eq_local]
  exact (fderiv_localFieldLift_cover P f z).symm

end EulerCylinderSmoothOrbit
end
end
