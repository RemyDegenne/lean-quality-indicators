namespace OAI

section

open scoped Real

open MeasureTheory

open scoped Topology

open MeasureTheory FourierTransform Convolution

open scoped SchwartzMap

open MeasureTheory FourierTransform TemperedDistribution

open scoped SchwartzMap Topology

open MeasureTheory TemperedDistribution FourierTransform LineDeriv

open scoped SchwartzMap ContDiff

open Filter Function

open scoped SchwartzMap Topology ContDiff

open MeasureTheory FourierTransform TemperedDistribution

open scoped SchwartzMap Topology ContDiff

open MeasureTheory

open scoped Topology ContDiff

open Matrix

open scoped ContDiff Matrix.Norms.Elementwise

open scoped ContDiff Topology

open Matrix

open scoped BigOperators Kronecker

noncomputable section

namespace TensorEstimate

open WeightedCalculus MomentCoordinates MomentDifferential MomentEquation Matrix MetricTensor

open scoped ContDiff

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma derivative_P_swap {φ f : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) (z : Space ι) :
    (fun p : Idx ι => pd p.2.1 (P φ f p.1 p.2.2) z) =
      act 1 1 (pulledH φ f z) (cube φ z) +
      act (hess φ z) (hess φ z) 1 (cube f (grad φ z)) := by
  ext ⟨a,l,k⟩
  change pd l (fun y => ∑ i, hess φ y a i * pulledH φ f y i k) z = _
  rw [pd_sum _ (fun i => (smooth_hess hφ a i).mul (smooth_pulledH hφ hf i k))]
  have hd (i : ι) := congrFun (pd_mul (smooth_hess hφ a i) (smooth_pulledH hφ hf i k) l) z
  simp_rw [hd]
  rw [Finset.sum_add_distrib]
  change _ = act 1 1 (pulledH φ f z) (cube φ z) (a,l,k) +
    act (hess φ z) (hess φ z) 1 (cube f (grad φ z)) (a,l,k)
  rw [act₃_apply, act₁₂_apply]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    change C φ l z a i * hess f (grad φ z) i k =
      hess f (grad φ z) k i * C φ i z a l
    rw [hess_symm hf _ i k, C_symm_last hφ l z a i,
      C_symm_first hφ l z i a, C_symm_last hφ i z l a]
    ring
  · apply Finset.sum_congr rfl
    intro i _
    change hess φ z a i * pd l ((fun x => hess f x i k) ∘ grad φ) z = _
    rw [pd_comp_grad (smooth_hess hf i k) hφ l, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    change hess φ z a i * (hess φ z l b * C f b (grad φ z) i k) =
      hess φ z a i * hess φ z l b * C f k (grad φ z) i b
    rw [C_symm_last hf b _ i k, C_symm_first hf b _ k i, C_symm_last hf k _ b i]
    ring

end TensorEstimate
end
end
end OAI
