section

@[expose] public section

noncomputable section

namespace EulerBaseDatum

open Set Filter ContinuousLinearMap MeasureTheory EulerSmoothLimit EulerVectorCalculus
  EulerSpatialCutoffs EulerGevrey EulerGevreyFunctions EulerLpTranslation
      EulerOperatorGevreyCalculus
  EulerMeanBoundary EulerMeanCutoffCurl EulerPacketPiola

open scoped ContDiff Topology

theorem vectorPotential_smooth (L : Space →L[ℝ] Space) : ContDiff ℝ ∞ (vectorPotential L) :=
  ContDiff.sum (fun i _ => (potential_smooth L i).smul contDiff_const)

end EulerBaseDatum
end
end
end
