public section

open Bundle Set ContinuousLinearMap Filter

open scoped Manifold Topology

section operations

variable {𝕜 B F M : Type*} {E : B → Type*}

variable
  -- Let `E` be a fiber bundle with base `B` and fiber `F` (a vector space over `𝕜`)
  [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
  [NormedAddCommGroup F] [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 F] [FiberBundle F E]
  -- Moreover let `E` be a vector bundle
  [(x : B) → AddCommGroup (E x)] [(x : B) → Module 𝕜 (E x)] [VectorBundle 𝕜 F E]
  -- Let the base `B` be charted over a fixed model space `HB`
  {HB : Type*} [TopologicalSpace HB] [ChartedSpace HB B]
  -- Moreover let `HB` be modelled on a normed space `EB` so that `B` (and hence `E`) have
  -- differentiable structures
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {I : ModelWithCorners 𝕜 EB HB}

variable {f : B → 𝕜} {a : 𝕜} {s t : Π x : B, E x} {u : Set B} {x₀ : B}

lemma mdifferentiable_smul_const_section
    (hs : MDiff (T% s)) : MDiff (T% (a • s)) :=
  fun x₀ ↦ (hs x₀).smul_const_section

end operations
end
