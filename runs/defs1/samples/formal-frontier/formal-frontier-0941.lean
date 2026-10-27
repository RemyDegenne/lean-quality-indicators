@[expose] public section

open CategoryTheory

universe u v

namespace CentralPolynomialSimplex

noncomputable section

variable {R : Type u} [Ring R]

/-- Evaluation of the coefficient polynomial at `x` times a tail. -/
def homotopyCoefficient (n : ℕ) (i : Fin (n + 1)) :
    Polynomial R →+* PolyRing (Polynomial R) (n + 1) :=
  Polynomial.eval₂RingHom'
    ((coefficient (R := Polynomial R) (n + 1)).comp Polynomial.C)
    (coefficient (R := Polynomial R) (n + 1) Polynomial.X * tail (n + 1) (i.val + 1))
    (fun r => by
      have hc : coefficient (R := Polynomial R) (n + 1) Polynomial.X *
          tail (R := Polynomial R) (n + 1) (i.val + 1) ∈
          Set.center (PolyRing (Polynomial R) (n + 1)) :=
        Set.mul_mem_center (polynomialX_mem_center (R := R) (n + 1))
          (tail_mem_center (R := Polynomial R) (n + 1) (i.val + 1))
      exact Semigroup.mem_center_iff.mp hc _)

end
end CentralPolynomialSimplex
end
