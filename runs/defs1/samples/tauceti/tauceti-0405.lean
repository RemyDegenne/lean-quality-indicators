public section

open CategoryTheory AlgebraicGeometry Opposite

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

variable (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]

/-- The **sheaf of relative differentials** `Ω_{X/R}` of a scheme `X` over a commutative ring
`R`: the sheafification of the presheaf `U ↦ Ω[Γ(X, U)⁄R]` of Kähler differentials. -/
def _root_.AlgebraicGeometry.Scheme.relativeDifferentials : X.Modules :=
  (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).obj
    (X.presheafRelativeDifferentials R)

end
end AlgebraicGeometry
end TauCeti
end
