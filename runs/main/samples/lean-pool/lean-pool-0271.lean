@[expose] public section

noncomputable section

namespace EulerCylinderDirichlet.Coefficients

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerTimeLp
  EulerVolterraConvolution EulerTimeH1FrameTransport EulerTerminalTimePrimitive
  EulerInitialTimePrimitive EulerTimeH1OperatorProduct EulerTransverseFixedEndpoint
  EulerTransverseEndpointParameter EulerTransverseEndpointCoordinates
  EulerTransverseGramInverse EulerTransverseForwardInverse
  EulerTransverseInitialCoordinates

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (P : ℝ) [Fact (0 < P)] {T : ℝ} (D : Coefficients T U E)

theorem endpointCoordinate_ae (Y : CylinderL2 P U) :
    (D.endpointSlope P Y : ℝ → CylinderL2 P U) =ᵐ[timeMeasure T]
      extendPath T D.time_pos.le (D.endpointCoordinate P Y) := by
  have ha := EulerFixedEndpointStrong.coordinateSlope_ae T D.time_pos.le
    (D.frame P) (D.frameDerivative P) (D.hessian P)
    D.lower D.lower_pos (D.frame_lower P) (D.frame_derivative P)
    D.potential D.potential_nonneg (D.hessian_upper P) D.small D.time_pos Y
  unfold endpointSlope
  filter_upwards [ha,ae_restrict_mem measurableSet_Icc] with t ht hmem
  exact (ht.trans ((D.endpointCoordinate_eq P Y ⟨t,hmem⟩).symm.trans
    (congrArg (D.endpointCoordinate P Y) (projIcc_of_mem D.time_pos.le hmem).symm)) :)

end EulerCylinderDirichlet.Coefficients
end
end
