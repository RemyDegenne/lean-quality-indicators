public section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme

variable {X : Scheme.{u}} [IsIntegral X]

namespace CartierDivisor

/-- The sheaf `𝒪_X(D)` of `𝒪_X`-modules attached to a Cartier divisor `D`. -/
def sheaf (D : CartierDivisor X) : X.Modules :=
  D.submodule.toSheafOfModules

end CartierDivisor
end Scheme
end
end AlgebraicGeometry
end TauCeti
end
