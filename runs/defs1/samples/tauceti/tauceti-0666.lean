public section

noncomputable section

open Set Function Topology Bundle

open scoped Manifold ContDiff InnerProductSpace

namespace TauCeti

variable {E V F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : WithTop ℕ∞} [IsManifold I 1 M] {f : M → V}

/-- The normal fibres form a fibre bundle with the topology inherited from `M × V`.
Use this definition as a local instance to choose its projected normal-coordinate atlas. -/
@[instance_reducible]
def normalFiberBundle (hf : ContMDiff I 𝓘(ℝ, V) 1 f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E) :
    FiberBundle F (fun x => normalSubspace I f x) where
  totalSpaceMk_isInducing' x := by
    rw [← (isEmbedding_totalSpace_normalSubspace (F := F) f).isInducing.of_comp_iff]
    exact isInducing_const_prod.mpr IsInducing.subtypeVal
  trivializationAtlas' := range (normalBundleTrivialization hf himm hdim)
  trivializationAt' := normalBundleTrivialization hf himm hdim
  mem_baseSet_trivializationAt' x := by simp
  trivialization_mem_atlas' x := mem_range_self x

end TauCeti
end
end
