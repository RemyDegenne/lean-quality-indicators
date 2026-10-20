public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.CurvedDGRightModuleCat

universe u

attribute [local implicit_reducible] ForgetEnrichment

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w} {M N : CurvedDGRightModuleCat.{u, u, u} h}
  (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N)

/-- The short complex `N → Cone(f) → M[1]` of closed cone maps. -/
noncomputable def coneShortComplex : ShortComplex
    (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)) :=
  ShortComplex.mk (coneInclusion f) (coneProjection f) (coneInclusion_comp_coneProjection f)

end TauCeti.CurvedDGRightModuleCat
end
