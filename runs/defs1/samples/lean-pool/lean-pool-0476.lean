@[expose] public section

noncomputable section

namespace EulerCylinderSobolevSpace

open EulerLiftedGradientSpace EulerPressureSpatialRegularity EulerSpatialSobolevInverse
  EulerCylinderSobolev EulerCylinderMollifier

open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- A translation-commuting L² operator acts on every actual derivative coordinate. -/
def liftOperator (q : ℕ) (A : LiftL2 period →L[ℝ] LiftL2 period)
    (hA : ∀ a f, A (translation period a f) = translation period a (A f)) :
    SobolevSpace period q →L[ℝ] SobolevSpace period q :=
  ((ContinuousLinearMap.pi (fun w : SobolevWord q => A.comp (ContinuousLinearMap.proj w))).comp
    (arrayOperator period q)).codRestrict (sobolevSubspace period q).toSubmodule (by
      intro u
      apply ClosedSubmodule.mem_iInf.mpr
      intro e
      have hd := A.hasFDerivAt.comp_hasDerivAt 0
        (word_hasDerivAt period u e.1.isLt e.2.1 e.2.2)
      change HasDerivAt (fun t => translation period
        (translationPath period (standardDirection e.2.2) t) (A (u.val (edgeParent e))))
        (A (u.val (edgeChild e))) 0
      simpa only [Function.comp_def, hA, word, edgeParent, edgeChild] using hd)

end EulerCylinderSobolevSpace
end
end
