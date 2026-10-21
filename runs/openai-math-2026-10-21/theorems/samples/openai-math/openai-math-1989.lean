namespace OAI

noncomputable section

namespace RVM

open MeasureTheory Set

open Filter Set

open scoped Topology

open scoped Topology ContDiff RealInnerProductSpace

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

open scoped Topology ContDiff NNReal

open Set Filter Metric MeasureTheory

open scoped Topology ContDiff

lemma sourceWaveKernel_secondTime {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (t s : ℝ) (x : Vec) :
    dirD (dirD (sourceWaveKernel ρ) ((1,0),0)) ((1,0),0) ((t,x),s) =
      deriv (deriv (fun r => waveK (fun y => ρ (s,y)) (r,x))) (t-s) := by
  have hK := contDiff_dirD (contDiff_sourceWaveKernel hρ) ((1,0),0)
  rw [← dirD_prod_left (hK.differentiable (by simp)) (1,0) (t,x) s]
  have hs : ContDiff ℝ ∞ (fun p => dirD (sourceWaveKernel ρ) ((1,0),0) (p,s)) :=
    hK.comp (contDiff_id.prodMk contDiff_const)
  rw [← deriv_slice_eq_dirD (hs.differentiable (by simp))]
  have he : (fun r => dirD (sourceWaveKernel ρ) ((1,0),0) ((r,x),s)) =
      fun r => deriv (fun u => waveK (fun y => ρ (s,y)) (u,x)) (r-s) := by
    funext r
    exact sourceWaveKernel_timeDerivative hρ r s x
  rw [he,deriv_comp_sub_const]

end RVM
end
end OAI
