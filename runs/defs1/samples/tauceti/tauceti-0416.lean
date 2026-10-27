public section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]

/-- Over an affine open `U`, the sections of the sheaf of relative differentials are the Kähler
differentials of the ring of functions: `Ω[Γ(X, U)⁄R] ≃ Γ(Ω_{X/R}, U)`, sending `D a` to `d a`
(`relativeDifferentialsSectionsEquiv_D`). -/
def relativeDifferentialsSectionsEquiv (U : X.affineOpens) :
    letI : Algebra R Γ(X, U) :=
      ((X.baseRingToStructurePresheaf R).app (op U.val)).hom.toAlgebra
    Ω[Γ(X, U)⁄R] ≃ₗ[Γ(X, U)] Γ(X.relativeDifferentials R, U) :=
  letI : Algebra R Γ(X, U) :=
    ((X.baseRingToStructurePresheaf R).app (op U.val)).hom.toAlgebra
  letI : U.property.fromSpec.IsOver (Spec (.of R)) := isOver_fromSpec R X U
  haveI : IsOpenImmersion U.property.fromSpec :=
    IsAffineOpen.isOpenImmersion_fromSpec U.property
  -- Pass through the affine chart `Spec Γ(X, U) ⟶ X`: the restriction comparison and the affine
  -- computation `Ω_{Spec A/R} ≅ Ω[A⁄R]~` identify the global sections of the restriction.
  (tilde.isoTop (.of Γ(X, U) Ω[Γ(X, U)⁄R]) ≪≫ moduleSpecΓFunctor.mapIso
    ((relativeDifferentialsSpecIso R Γ(X, U)).symm ≪≫
      (relativeDifferentialsRestrictIso R U.property.fromSpec).symm)).toLinearEquiv.trans
    ((X.relativeDifferentials R).fromSpecSectionsEquiv U.property).symm

end
end TauCeti.AlgebraicGeometry
end
