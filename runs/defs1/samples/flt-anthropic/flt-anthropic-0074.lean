namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_iterCech_cols_exact_of_isQuasicoherent

attribute [-instance] AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace G4Sol

p2m_open

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} (π : Z ⟶ Spec (.of R)) (N : Z.Modules)

variable (𝔄 𝔅 : Z.OrderedOpenFamily) (ℭ : Z.OrderedOpenFamily)

local notation "FZ" => OModulePresheaf.ofModules π N

variable (haff : ∀ i j, IsAffineOpen (𝔄.U i ⊓ 𝔅.U j))

variable (hcov : ⨆ ij : 𝔄.ι × 𝔅.ι, 𝔄.U ij.1 ⊓ 𝔅.U ij.2 = ⊤)

variable {C : Z.Opens}

section Column

variable (C : Z.Opens)

local notation "𝔘" => 𝔅.restr C

local notation "DK" => OModulePresheaf.biCech (OModulePresheaf.ofModules π N) 𝔄 (𝔅.restr C)

abbrev OA : (p : ℕ) → 𝔄.Idx p → Z.Opens := fun _ s => 𝔄.inter s ⊓ C

end Column
end G4Sol
end P2MW.S_AlgebraicGeometry_OModulePresheaf_iterCech_cols_exact_of_isQuasicoherent
