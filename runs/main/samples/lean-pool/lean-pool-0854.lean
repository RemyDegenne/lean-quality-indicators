@[expose] public section

namespace CompactSelfAdjoint

open CompactSpectral

open Set Filter Topology

open scoped Topology

open Metric

variable {𝕜 : Type*} [RCLike 𝕜]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

section

variable [Nontrivial E]

omit [Nontrivial E] in
lemma exists_reApplyInnerSelf_ne_zero_of_isSelfAdjoint
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (h0 : T ≠ 0) : ∃ x : E, T.reApplyInnerSelf x ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hSym : (T : E →ₗ[𝕜] E).IsSymmetric := IsSelfAdjoint.isSymmetric hT
  have hinner0 : ∀ x : E, inner 𝕜 (T x) x = 0 := by
    intro x
    have hRe : (T.reApplyInnerSelf x : 𝕜) = inner 𝕜 (T x) x := by
      simpa [ContinuousLinearMap.reApplyInnerSelf_apply] using
        (LinearMap.IsSymmetric.coe_re_inner_apply_self (T := (T : E →ₗ[𝕜] E)) hSym x)
    simp_all
  have hinner : ∀ x y : E, inner 𝕜 ((T : E →ₗ[𝕜] E) x) y = 0 := by
    intro x y
    have hpol :=
      LinearMap.IsSymmetric.inner_map_polarization (𝕜 := 𝕜) (E := E) (T := (T : E →ₗ[𝕜] E)) hSym x y
    have hxy : inner 𝕜 ((T : E →ₗ[𝕜] E) (x + y)) (x + y) = 0 := by
      simpa using hinner0 (x + y)
    have hxmy : inner 𝕜 ((T : E →ₗ[𝕜] E) (x - y)) (x - y) = 0 := by
      simpa using hinner0 (x - y)
    have hxIy :
        inner 𝕜 ((T : E →ₗ[𝕜] E) (x + (RCLike.I : 𝕜) • y)) (x + (RCLike.I : 𝕜) • y) = 0 := by
      simpa using hinner0 (x + (RCLike.I : 𝕜) • y)
    have hxmIy :
        inner 𝕜 ((T : E →ₗ[𝕜] E) (x - (RCLike.I : 𝕜) • y)) (x - (RCLike.I : 𝕜) • y) = 0 := by
      simpa using hinner0 (x - (RCLike.I : 𝕜) • y)
    simp_all
  have hTzero : T = 0 := by
    ext x
    have : ∀ v : E, inner 𝕜 v (T x) = 0 := by
      simp_all
    apply ext_inner_left 𝕜
    simp_all
  exact h0 hTzero

end
end CompactSelfAdjoint
end
