namespace OAI

universe uF

section

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal Topology ContDiff Laplacian

namespace Bernoulli

open scoped _root_.Bernoulli

variable {d : ℕ} {D : Set (Space d)}

namespace GroundState

open Halfspace

lemma integral_norm_sq_eq {F : Type uF} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {μ : Measure (Space d)} {f : Space d → F} (hf : MemLp f 2 μ) :
    (∫x, ‖f x‖^2 ∂μ)=‖hf.toLp f‖^2 := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx,real_inner_self_eq_norm_sq]

end GroundState
end Bernoulli
end
end
end OAI
