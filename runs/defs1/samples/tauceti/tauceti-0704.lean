public section

open AlgebraicGeometry CategoryTheory WithConv

open scoped CategoryTheory.MonObj

namespace TauCeti.GeneralLinear

universe u w w'

variable {R : Type u} [CommRing R] {N : ℕ}

section Points

variable {A : Type w} [CommRing A] [Algebra R A]

/-- The diagonal-torus homomorphism on `A`-points.  Under the split-torus and general-linear
points equivalences it is the diagonal embedding `diagGL : (Fin N → Aˣ) →* GL (Fin N) A`. -/
noncomputable def diagonalTorusPoints :
    WithConv (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ)) →ₐ[R] A) →*
      WithConv (coordinateHopfAlgebra R N →ₐ[R] A) :=
  (pointsMulEquiv (R := R) (A := A) N).symm.toMonoidHom.comp
    ((diagGL (k := A)).comp
      ((diagonalTorusCoordinates (N := N) (A := A)).comp
        (SplitTorus.pointsMulEquiv (R := R) (A := A)).toMonoidHom))

end Points
end TauCeti.GeneralLinear
end
