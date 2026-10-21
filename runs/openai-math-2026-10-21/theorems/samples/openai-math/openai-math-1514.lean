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

lemma laplace_slice_eq_dirD {F : ℝ × Vec → ℝ} (hF : ContDiff ℝ ∞ F) (t : ℝ) (x : Vec) :
    laplace (fun y => F (t,y)) x =
      ∑ i : Fin 3, dirD (dirD F (0,basis i)) (0,basis i) (t,x) := by
  rw [laplace_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun y => spatialPartial (fun z => F (t,z)) y i) =
      fun y => dirD F (0,basis i) (t,y) := by
    funext y
    exact spatialPartial_time_slice (hF.differentiable (by simp) (t,y)) i
  rw [he]
  exact spatialPartial_time_slice ((contDiff_dirD hF (0,basis i)).differentiable (by simp) (t,x)) i

end RVM
end
end OAI
