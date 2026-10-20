public section

open CategoryTheory AlgebraicGeometry Opposite

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

variable (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]

variable {X} in
/-- The `R`-derivations of the structure sheaf of a scheme `X` over `R` with values in a sheaf
of `𝒪_X`-modules `M`: compatible families of `R`-linear derivations `Γ(X, U) → Γ(M, U)`. -/
abbrev _root_.AlgebraicGeometry.Scheme.Modules.Derivation (M : X.Modules) : Type u :=
  PresheafOfModulesOfCommRing.Derivation' (R := X.presheaf) M.val
    (X.baseRingToStructurePresheaf R)

end
end AlgebraicGeometry
end TauCeti
end
