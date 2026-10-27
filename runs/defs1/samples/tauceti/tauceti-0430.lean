public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S) {A : Type*} [Group A]

variable {E} {φ : A →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)}

section NaiveLocus

variable {H : Over S} (u : A →* (H ⟶ Over.mk E.structureMap))

/-- The naive locus of `u`, for a finite group `A`, as an open subscheme of `H`. -/
def naiveLocusOpens [Finite A] : H.left.Opens :=
  ⟨naiveLocus u, isOpen_naiveLocus u⟩

end NaiveLocus
end TauCeti.AlgebraicGeometry.EllipticCurveGeom
end
