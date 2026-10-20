@[expose] public section

open CategoryTheory

universe u v

namespace CentralPolynomialSimplex

noncomputable section

variable {R : Type u} [Ring R]

@[simp] theorem coordinate_zero (n : ℕ) : coordinate (R := R) n 0 =
    1 - ∑ j : Fin n, generator (R := R) n j := rfl

end
end CentralPolynomialSimplex
end
