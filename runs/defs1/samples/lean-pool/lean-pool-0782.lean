@[expose] public section

noncomputable section

namespace EulerPacketCylinderField.Field

open Set MeasureTheory ContinuousLinearMap Finset EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSmoothOrbit EulerLpCylinderTranslation EulerMetricTransport
      EulerPacketProfileRecursion

open scoped ContDiff

variable {P T : ℝ} [Fact (0 < P)] {raw raw' : VectorField}

/-- Zero, constructed using `ofLifted`. -/
def zero (P T : ℝ) [Fact (0 < P)] : Field P T (0 : VectorField) :=
  ofLifted 0 (by simpa only [map_zero] using (contDiff_const :
      ContDiff ℝ ∞ (fun _ : LiftTangent => (0 : C(Icc (0 : ℝ) T,LiftL2 P)))))
    (fun _ _ => 0) (fun _ => continuous_const)
    (fun _ => Lp.coeFn_zero Space 2 (liftMeasure P)) (fun _ _ _ => rfl)

end EulerPacketCylinderField.Field
end
end
