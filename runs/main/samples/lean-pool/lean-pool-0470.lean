section

@[expose] public section

noncomputable section

namespace EulerTransversePacketPrimary

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerCylinderFieldReflection
  EulerTransversePacketProvider EulerTimeIntervalRestriction EulerElapsedTimePathGluing

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) (Y : InitialData P D)
  (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
  (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
  (hM : ∀ t x, D.M.field t (-x) = D.M.field t x)
  (hH : ∀ t x, B.H.field t (-x) = B.H.field t x)
  (hY : reflection (V := U) P (Y.value : CylinderL2 P U) = -(Y.value : CylinderL2 P U))

include hF hM hH hY

include hSym

theorem futureDerivative_reflection_neg (t : Icc (0 : ℝ) (D.T - τ)) :
    reflection (V := Vector3) P (futureDerivative τ hτ hτT B Y t) =
      -futureDerivative τ hτ hτT B Y t :=
  (zeroForcing (D.tail τ hτ.le hτT)).derivativePath_reflection_neg (forwardInitial τ hτ hτT B Y)
      hSym
    (fun s x => hF (tailInclusion D.T τ hτ.le s) x)
    (fun s x => hM (tailInclusion D.T τ hτ.le s) x)
    (by intro s x θ; simp only [Pi.zero_apply,neg_zero])
    (forwardInitial_reflection_neg τ hτ hτT B Y hF hM hH hY) t

end EulerTransversePacketPrimary
end
end
end
