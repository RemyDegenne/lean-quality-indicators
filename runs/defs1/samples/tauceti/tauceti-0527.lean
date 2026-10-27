public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S) {A : Type*} [Group A]

variable {E} {φ : A →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)}

section NaiveLocus

variable {H : Over S} (u : A →* (H ⟶ Over.mk E.structureMap))

/-- **The naive locus of a family of homomorphisms.** For an elliptic curve `E` over a scheme `S`, a
scheme `H` over `S` and a homomorphism `u : A →* E(H)` to the group of points of `E` with values in
`H`, the set of points `h` of `H` at which `u` is injective on the fibre: for every `a ≠ 1`, the
point `u a` misses the zero section of `E` at `h`. -/
def naiveLocus : Set H.left :=
  {h | ∀ a, a ≠ 1 → (u a).left h ≠ E.zero (H.hom h)}

end NaiveLocus
end TauCeti.AlgebraicGeometry.EllipticCurveGeom
end
