namespace OAI

noncomputable section

open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory

open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Transport

open ContinuousLinearMap Set

open scoped ContDiff InnerProductSpace Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma contDiff_mixedSigma {A : E × E → ℝ} {j : E × E → E × E}
    (hA : ContDiff ℝ ∞ A) (hj : ContDiff ℝ ∞ j) : ContDiff ℝ ∞ (mixedSigma A j) :=
  (hA.comp hj).add ((hj.fst.sub contDiff_fst).inner ℝ contDiff_snd)

end NearbyLagrangian.Transport
end
end OAI
