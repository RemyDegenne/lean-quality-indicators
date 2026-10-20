@[expose] public section

noncomputable section

open Set Fin Filter Function

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {s : Set E} {t : Set F}
  {q : F → FormalMultilinearSeries 𝕜 F G} {p : E → FormalMultilinearSeries 𝕜 E F}

namespace OrderedFinpartition

variable {n : ℕ} (c : OrderedFinpartition n)

attribute [local instance] neZero_length neZero_partSize

variable (𝕜 E F G) in
/-- Bundled version of `compAlongOrderedFinpartition`, depending continuously linearly on `f`
and continuously multilinearly on `p`. -/
noncomputable def compAlongOrderedFinpartitionL :
    (F [×c.length]→L[𝕜] G) →L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun i ↦ E [×c.partSize i]→L[𝕜] F) (E [×n]→L[𝕜] G) := by
  refine MultilinearMap.mkContinuousLinear c.compAlongOrderedFinpartitionₗ 1 fun f p ↦ ?_
  simp only [one_mul, compAlongOrderedFinpartitionₗ_apply_apply]
  apply norm_compAlongOrderedFinpartition_le

end OrderedFinpartition
end
end
