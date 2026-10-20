public section

open ContinuousLinearMap

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable {f : E → F}

variable {f' : E →L[𝕜] F}

variable {x : E}

variable {s : Set E}

section ContinuousMultilinearApplyConst

variable {ι : Type*}
  {M : ι → Type*} [∀ i, NormedAddCommGroup (M i)] [∀ i, NormedSpace 𝕜 (M i)]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  {c : E → ContinuousMultilinearMap 𝕜 M H}
  {c' : E →L[𝕜] ContinuousMultilinearMap 𝕜 M H}

section finite

variable [Finite ι]

@[fun_prop]
theorem DifferentiableOn.continuousMultilinear_apply_const (hc : DifferentiableOn 𝕜 c s)
    (u : ∀ i, M i) : DifferentiableOn 𝕜 (fun y ↦ (c y) u) s :=
  fun x hx ↦ (hc x hx).continuousMultilinear_apply_const u

end finite
end ContinuousMultilinearApplyConst
end
end
