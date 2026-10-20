public section

open Filter Asymptotics ContinuousLinearMap Set

open scoped Topology

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]

variable {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

variable {f f₀ f₁ : E → F}

variable {f' f₀' f₁' g' : E →L[𝕜] F}

variable {x : E}

variable {s t : Set E}

variable {L : Filter (E × E)}

section congr

theorem hasFDerivWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) :
    HasFDerivWithinAt f f' s x ↔ HasFDerivWithinAt f f' t x :=
  hasFDerivWithinAt_congr_set_nhdsNE <| h.filter_mono inf_le_left

end congr
end
end
