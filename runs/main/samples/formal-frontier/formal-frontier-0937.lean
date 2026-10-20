open AlgebraicGeometry CategoryTheory

open scoped ProjectiveSpace LinearAlgebra.Projectivization

public section

noncomputable section

namespace ProjectiveSpace

universe u v

variable {k : Type u} [Field k] [IsAlgClosed k]

variable {ι : Type v} [Fintype ι]

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "𝒜" => MvPolynomial.homogeneousSubmodule ι k

@[simp]
theorem projectivizationEquivClosedPoints_apply (x : Projectivization k (ι → k)) :
    (projectivizationEquivClosedPoints x).1 = projectivizationToProj x :=
  rfl

end ProjectiveSpace
end
end
