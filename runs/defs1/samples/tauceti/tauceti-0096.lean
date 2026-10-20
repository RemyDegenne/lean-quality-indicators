public section

open AlgebraicGeometry CategoryTheory Order

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.CartierDivisor

variable {X Y : Scheme.{u}} [IsIntegral X] [IsNoetherian X]

/-- The degree of a Cartier divisor relative to `f`, obtained by weighting its orders at
codimension-one points by their residue degrees. -/
def relativeDegree (f : X ⟶ Y) : CartierDivisor X →+ ℤ :=
  (SchemeWeilDivisor.relativeDegree f).comp (toWeilDivisorHom : CartierDivisor X →+ _)

end Scheme.CartierDivisor
end
end TauCeti.AlgebraicGeometry
end
