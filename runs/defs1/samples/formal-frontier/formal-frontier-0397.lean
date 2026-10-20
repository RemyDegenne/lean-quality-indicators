set_option autoImplicit false

set_option relaxedAutoImplicit false

set_option linter.mathlibStandardSet true

set_option linter.style.header false

@[expose] public noncomputable section

open scoped BigOperators

open TensorProduct

universe u v v' w w'

namespace HopfAlgebra

section CoefficientMatrix

variable {R : Type u} {A : Type v} {ι : Type w}
  [CommSemiring R] [Semiring A] [HopfAlgebra R A]
  [Fintype ι] [DecidableEq ι]
  (M : Matrix ι ι A)
  (hΔ : ∀ i j, Coalgebra.comul (R := R) (M i j) = ∑ k, M i k ⊗ₜ[R] M k j)
  (hε : ∀ i j, Coalgebra.counit (R := R) (M i j) = if i = j then 1 else 0)

include hΔ hε

/-- A finite Hopf coefficient matrix as a unit, with entrywise antipode as inverse. -/
def coefficientMatrixUnit : (Matrix ι ι A)ˣ :=
  Units.mk M (M.map (antipode R))
    (coefficientMatrix_mul_antipode M hΔ hε)
    (antipode_mul_coefficientMatrix M hΔ hε)

end CoefficientMatrix
end HopfAlgebra
end
