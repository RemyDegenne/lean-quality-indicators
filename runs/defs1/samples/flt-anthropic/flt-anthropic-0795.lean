namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_iterCech_cols_exact_of_isQuasicoherent

attribute [-instance] AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace LAV

p2m_open

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} (π : Z ⟶ Spec (.of R)) (N : Z.Modules)

variable (W : Z.Opens) (𝔘 : Z.OrderedOpenFamily) (O : (p : ℕ) → 𝔘.Idx p → Z.Opens)

variable (hOface : ∀ (p : ℕ) (s : 𝔘.Idx (p + 1)) (j : Fin (p + 2)), O (p + 1) s ≤ O p (𝔘.face s j))

def eSlot (hUaff : ∀ i, IsAffineOpen (𝔘.U i ⊓ W)) (hcovW : W ≤ ⨆ i, 𝔘.U i)
    (hO₁ : ∀ (p : ℕ) (s : 𝔘.Idx p), O p s ≤ 𝔘.inter s ⊓ W)
    (hO₂ : ∀ (p : ℕ) (s : 𝔘.Idx p), 𝔘.inter s ⊓ W ≤ O p s) (p : ℕ) (s : 𝔘.Idx p) :
    (OModulePresheaf.ofModules π N).obj (O p s) ≃ₗ[R]
      (OModulePresheaf.ofModules (W.ι ≫ π) (N.restrict W.ι)).obj
        ((coverW W 𝔘 hUaff hcovW).inter (show (coverW W 𝔘 hUaff hcovW).Idx p from s)) :=
  eEntry π N W _ _ (image_inter_coverW W 𝔘 O hUaff hcovW hO₁ hO₂ p s)

end LAV
end P2MW.S_AlgebraicGeometry_OModulePresheaf_iterCech_cols_exact_of_isQuasicoherent
