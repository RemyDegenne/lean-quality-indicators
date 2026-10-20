public section

namespace TauCeti

universe uk uA uM w

variable {k : Type uk} {A : Type uA} [CommRing k] [Ring A] [Algebra k A]

variable (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]

variable {M : Type uM} [AddCommGroup M] [Module k M] [Module A M] (G : InternalGrading k M)

attribute [instance] addCommGroup module moduleBase isScalarTower gradedSMul

namespace GradedProjectiveResolution

universe ui uN uX

variable {𝒜}

variable {ι : Type ui} {N : ι → Type uN}
  [∀ i, AddCommGroup (N i)] [∀ i, Module k (N i)] [∀ i, Module A (N i)]
  [∀ i, IsScalarTower k A (N i)]
  (G : ∀ i, InternalGrading k (N i)) [∀ i, SetLike.GradedSMul 𝒜 (G i).piece]
  (r : ∀ i, GradedProjectiveResolution.{uk, uA, uN, uX} 𝒜 (G i))

/-- The componentwise direct sum of a family of graded projective resolutions. Its terms,
differentials and augmentation are direct sums of the corresponding component data. -/
noncomputable abbrev directSum :
    GradedProjectiveResolution 𝒜 (InternalGrading.directSum G) where
  X n := DirectSum ι fun i ↦ (r i).X n
  grading n := InternalGrading.directSum fun i ↦ (r i).grading n
  gradedSMul n := ⟨fun {_ _} _ _ ha hx ↦ by
    rw [InternalGrading.directSum_piece, InternalGrading.mem_directSumPiece_iff] at hx ⊢
    exact fun i ↦ SetLike.GradedSMul.smul_mem (B := ((r i).grading n).piece) ha (hx i)⟩
  projective n := Module.Projective.directSum_iff.mpr fun i ↦ (r i).projective n
  d n := DirectSum.lmap fun i ↦ (r i).d n
  «π» := DirectSum.lmap fun i ↦ (r i).π
  isHomogeneous_d n := LinearMap.isHomogeneous_def.2 fun p x hx ↦ by
    rw [InternalGrading.directSum_piece, InternalGrading.mem_directSumPiece_iff] at hx ⊢
    exact fun i ↦ by
      rw [DirectSum.lmap_apply]
      simpa using ((r i).isHomogeneous_d n).map_mem (hx i)
  isHomogeneous_π := LinearMap.isHomogeneous_def.2 fun p x hx ↦ by
    rw [InternalGrading.directSum_piece, InternalGrading.mem_directSumPiece_iff] at hx ⊢
    exact fun i ↦ by
      rw [DirectSum.lmap_apply]
      simpa using (r i).isHomogeneous_π.map_mem (hx i)
  surjective_π := (DirectSum.lmap_surjective _).2 fun i ↦ (r i).surjective_π
  exact_d_π := Function.Exact.directSum fun i ↦ (r i).exact_d_π
  exact_d_d n := Function.Exact.directSum fun i ↦ (r i).exact_d_d n

end GradedProjectiveResolution
end TauCeti
end
