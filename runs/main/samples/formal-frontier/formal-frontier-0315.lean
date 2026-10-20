@[expose] public section

universe u v

open CategoryTheory

universe uS

namespace KTheory

namespace K0

section LocalDimension

variable (R : Type u) [Ring R] [IsLocalRing R]

@[simp]
theorem localDimensionHom_of_self : localDimensionHom R (of R Rᵐᵒᵖ) = 1 := by
  let : (Ring.jacobson R).IsMaximal := IsLocalRing.isMaximal_ringJacobson R
  let : DivisionRing (R ⧸ Ring.jacobson R) :=
    Ideal.Quotient.divisionRing (Ring.jacobson R)
  exact finrankHom_map_of_self (Ideal.Quotient.mk (Ring.jacobson R))

end LocalDimension
end K0
end KTheory
end
