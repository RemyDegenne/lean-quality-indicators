public section

open Module

namespace TauCeti

universe u

variable {R K V : Type*} [CommRing R] [IsDomain R]

variable [Field K] [Algebra R K] [IsFractionRing R K] [Module.IsTorsionFree R K]

variable [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/-- The canonical pairing between the dual submodule of a free full lattice and the lattice
itself is a linear equivalence over `R` whenever the ambient bilinear form is nondegenerate. -/
noncomputable def _root_.LinearMap.BilinForm.dualSubmoduleEquivDual
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (N : Submodule R V) [hN : N.IsLattice K] [Module.Free R N] :
    B.dualSubmodule N ≃ₗ[R] Module.Dual R N :=
  LinearEquiv.ofBijective (B.dualSubmoduleToDual N)
    ⟨B.dualSubmoduleToDual_injective hB N hN.span_eq_top,
      LinearMap.BilinForm.dualSubmoduleToDual_surjective B hB N⟩

end TauCeti
end
