namespace OAI

noncomputable section

open MeasureTheory Set

open Filter Set

open scoped Topology

open scoped Topology Pointwise

open Set MeasureTheory Metric ODE

open scoped Topology NNReal

open scoped ContDiff

open Set MeasureTheory Metric

open Set MeasureTheory

open Set MeasureTheory Metric Filter ODE

open Set MeasureTheory Filter Metric ODE

open Set MeasureTheory Filter Metric

open scoped Topology NNReal ContDiff

open Set MeasureTheory Filter

open scoped Topology ContDiff RealInnerProductSpace NNReal

open Set Filter MeasureTheory Metric

open scoped Topology ContDiff RealInnerProductSpace

open scoped Topology ContDiff NNReal RealInnerProductSpace

open scoped Topology ContDiff NNReal

open scoped Topology ContDiff ENNReal

open Set

open Set Filter Metric MeasureTheory

open scoped Topology ContDiff

namespace RVM

lemma continuousOn_normalisedElectricKernel {H : Type*} [TopologicalSpace H]
    {r : H → ℝ} {n u b : H → Vec} {S : Set H}
    (hr : ContinuousOn r S) (hn : ContinuousOn n S) (hu : ContinuousOn u S)
    (hb : ContinuousOn b S) (hd : ∀ z ∈ S, 1-dot (n z) (u z)≠0) :
    ContinuousOn (fun z => normalisedElectricKernel (r z) (n z) (u z) (b z)) S := by
  have hdot (f g : H → Vec) (hf : ContinuousOn f S) (hg : ContinuousOn g S) :
      ContinuousOn (fun z => dot (f z) (g z)) S :=
    (contDiff_dot_pair (k:=1)).continuous.comp_continuousOn (hf.prodMk hg)
  have hD : ContinuousOn (fun z => 1-dot (n z) (u z)) S :=
    continuousOn_const.sub (hdot n u hn hu)
  have hp : ∀ z ∈ S, (1-dot (n z) (u z))^3≠0 := fun z hz => pow_ne_zero 3 (hd z hz)
  exact (((continuousOn_const.sub (hdot u u hu hu)).div (hD.pow 3) hp).smul (hn.sub hu)).add
    ((hr.div (hD.pow 3) hp).smul (((hdot n b hn hb).smul (hn.sub hu)).sub (hD.smul hb)))

end RVM
end
end OAI
