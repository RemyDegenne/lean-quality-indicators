public section

open AlgebraicGeometry CategoryTheory WithConv

open scoped CategoryTheory.MonObj

namespace TauCeti.Symplectic

universe u v w

variable {R : Type u} [CommRing R] {m : ℕ}

section Points

variable {A : Type w} [CommRing A] [Algebra R A]

/-- **The diagonal torus of `Sp₂ₘ` on algebra-valued points.** Under the split-torus and
symplectic points equivalences it is the standard diagonal matrix with paired inverse entries. -/
noncomputable def diagonalTorusPoints :
    WithConv (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ)) →ₐ[R] A) →*
      WithConv (coordinateHopfAlgebra R m →ₐ[R] A) :=
  (pointsMulEquiv (R := R) (A := A) m).symm.toMonoidHom.comp
    (GLSymplecticFin.diagonal.comp
      ((GeneralLinear.diagonalTorusCoordinates (N := m) (A := A)).comp
        (SplitTorus.pointsMulEquiv (R := R) (A := A)).toMonoidHom))

end Points
end TauCeti.Symplectic
end
