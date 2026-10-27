public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj
  Opposite

universe u

namespace TauCeti.AlgebraicGeometry

namespace EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)

variable {E} {Z : Over S} {x : Z ⟶ Over.mk E.structureMap} {N : ℕ}

variable (E)

variable {E}

section Representable

variable (hN : ∀ s : S, (N : S.residueField s) ≠ 0)

variable (P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap)

/-- The inclusion of the locus where `P` has naive exact order `N` into `S`. -/
noncomputable def naiveExactOrderPreimageι : naiveExactOrderPreimage hN P ⟶ S :=
  pullback.fst _ _

end Representable
end EllipticCurveGeom
end TauCeti.AlgebraicGeometry
end
