public section

open Filter Asymptotics ContinuousLinearMap Set NNReal

open scoped Topology

open scoped Pointwise

section SMulLeft

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {s : Set E}
  {f' : E →L[𝕜] F} {x : E}

theorem fderiv_comp_smul (c : 𝕜) : fderiv 𝕜 (f <| c • ·) x = c • fderiv 𝕜 f (c • x) := by
  rw [← fderivWithin_univ, fderivWithin_comp_smul _ uniqueDiffWithinAt_univ]
  rcases eq_or_ne c 0 with rfl | hc <;> simp [smul_set_univ₀, *]

end SMulLeft
end
