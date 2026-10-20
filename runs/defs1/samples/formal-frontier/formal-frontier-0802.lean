@[expose] public section

open Bundle

namespace Bundle.ContinuousHermitianMetric

universe u𝕜 uB uF uG uE

variable {𝕜 : Type u𝕜} [RCLike 𝕜] {B : Type uB} [TopologicalSpace B]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type uG} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {E : B → Type uE} [∀ b, TopologicalSpace (E b)]
  [∀ b, AddCommGroup (E b)] [∀ b, Module 𝕜 (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E]
  (g : ContinuousHermitianMetric 𝕜 F E) (S : ∀ b, Submodule 𝕜 (E b))
  [TopologicalSpace (TotalSpace G (fun b ↦ S b))]
  [FiniteDimensional 𝕜 F]
  [FiberBundle G (fun b ↦ S b)] [VectorBundle 𝕜 G (fun b ↦ S b)]
  (hS : Topology.IsEmbedding
    (fun p : TotalSpace G (fun b ↦ S b) ↦ TotalSpace.mk' F p.proj (p.2 : E p.proj)))

local notation "C" => (fun b ↦ Submodule.orthogonalBilin
  (ContinuousLinearMap.toLinearMap₁₂ (ContinuousHermitianMetric.inner g b)) (S b))

local notation "H" => EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 F - Module.finrank 𝕜 G))

local notation "tC" => TopologicalSpace.induced
  (fun p : TotalSpace H C ↦ TotalSpace.mk' F (TotalSpace.proj p)
    (Subtype.val (TotalSpace.snd p))) inferInstance

local notation "tProd" => @FiberBundle.Prod.topologicalSpace B G (fun b ↦ S b) H C
  inferInstance tC

local notation "Φ" => @Homeomorph.toEquiv _ _ tProd inferInstance
  (g.orthogonalAdditionHomeomorph S hS)

/-- The continuous total-space projection onto the metric orthogonal family of an
embedded intrinsic submodule bundle. The target has the ambient-induced total
topology. Its function is the second total projection after inverse addition. -/
noncomputable def orthogonalComplementProjectionTotal :
    @ContinuousMap (TotalSpace F E) (TotalSpace H C) inferInstance tC := by
  letI : TopologicalSpace (TotalSpace H C) := tC
  exact
    { toFun := (fun p : TotalSpace (G × H) ((fun b ↦ S b) ×ᵇ C) ↦
        TotalSpace.mk' H p.proj p.2.2) ∘ (Φ).symm
      continuous_toFun := by
        exact (FiberBundle.Prod.isInducing_diag G (fun b ↦ S b) H C).continuous.snd.comp
          (g.orthogonalAdditionHomeomorph S hS).continuous_invFun }

end Bundle.ContinuousHermitianMetric
end
