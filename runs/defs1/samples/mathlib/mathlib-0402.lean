open scoped Finset

@[expose] public section

open NormedField Set Seminorm TopologicalSpace Filter List Bornology

open NNReal Pointwise Topology Uniformity

variable {R 𝕜 𝕜₂ 𝕝 𝕝₂ E F G ι ι' : Type*}

section NormedSpace

variable [NormedField 𝕜] [ha : AddCommGroup E] [hm : Module 𝕜 E]
  [t : TopologicalSpace E] [hn : IsNormableSpace 𝕜 E]

variable (𝕜 E)

/-- A normable space can be endowed with a seminorm defining the same topology. -/
noncomputable abbrev IsNormableSpace.toSeminormedAddCommGroup : SeminormedAddCommGroup E := by
  let : Norm E := ⟨IsNormableSpace.seminorm 𝕜 E⟩
  let c : SeminormedSpace.Core 𝕜 E :=
  { norm_nonneg x := apply_nonneg _ x
    norm_smul c x := map_smul_eq_mul _ c x
    norm_triangle x y := map_add_le_add _ x y }
  refine SeminormedAddCommGroup.ofCoreReplaceTopology c ?_
  rw [hn.withSeminorms_seminorm.topologicalSpace_eq_iInf, ciInf_unique]

end NormedSpace
end
