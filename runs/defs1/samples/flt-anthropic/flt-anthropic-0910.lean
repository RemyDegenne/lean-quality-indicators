namespace P2MW.S_NeronModelInfra_exists_mul_extension_isIso_lift_of_forall_dense_preimage_fibre_of_forall_mem_opens_of_section

set_option autoImplicit false

set_option linter.unusedSimpArgs false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

universe u

namespace P2mGExt

attribute [scoped instance] Chunk.Φ_open Chunk.Ψ_open Chunk.y_smooth Chunk.y_sep Chunk.π₁_smooth Chunk.π₂_smooth
  Chunk.π₁_surj Chunk.π₂_surj

namespace Chunk

variable {R : Type u} [CommRing R] (D : Chunk R)

scoped instance smooth_outer : Smooth D.outer := MorphismProperty.of_isPullback D.isPullback_P12_outer inferInstance

scoped instance surjective_outer : Surjective D.outer :=
  MorphismProperty.of_isPullback D.isPullback_P12_outer inferInstance

scoped instance : IsOpenImmersion D.jM :=
  MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance rfl rfl

scoped instance smooth_pM : Smooth D.pM := by rw [pM]; infer_instance

section Division

variable (M : D.P ⟶ D.Y) (hMm : D.U.ι ≫ M = D.m) (hMy : M ≫ D.y = D.π₁ ≫ D.y)

def jD : D.ZD ⟶ D.Y3 :=
  pullback.map D.m (D.U.ι ≫ D.π₁) D.π₂ D.π₁ D.Φ D.Φ (𝟙 D.Y)
    ((Category.comp_id _).trans D.Φ_snd.symm) ((Category.comp_id _).trans D.Φ_fst.symm)

end Division
end Chunk
end P2mGExt
end
end P2MW.S_NeronModelInfra_exists_mul_extension_isIso_lift_of_forall_dense_preimage_fibre_of_forall_mem_opens_of_section
