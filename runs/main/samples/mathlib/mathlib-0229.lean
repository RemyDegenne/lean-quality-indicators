public noncomputable section

open ContinuousLinearMap InnerProductSpace Submodule Filter

open scoped ComplexConjugate Topology

namespace RKHS

variable {𝕜 : Type*} [RCLike 𝕜]

variable {X : Type*}

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

variable [RKHS 𝕜 H X V]

variable (H) [CompleteSpace H] [CompleteSpace V]

lemma norm_kerFun_eq_sqrt_norm_kernel (x) : ‖kerFun H x‖ = √‖kernel H x x‖ := by
  rw [norm_kernel_eq_norm_kerFun_sq, Real.sqrt_sq (norm_nonneg _)]

end RKHS
end
