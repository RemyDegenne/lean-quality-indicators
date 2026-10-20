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

def divl : (D.V : Scheme.{u}) ⟶ D.Y := D.linv ≫ D.U.ι ≫ D.π₂

end Chunk
end P2mGExt
end
end P2MW.S_NeronModelInfra_exists_mul_extension_isIso_lift_of_forall_dense_preimage_fibre_of_forall_mem_opens_of_section
