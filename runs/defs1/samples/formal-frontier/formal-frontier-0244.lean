@[expose] public section

open CategoryTheory

universe u v

namespace CentralPolynomialSimplex

noncomputable section

variable {R : Type u} [Ring R]

/-- Homogeneous coordinates, including the eliminated zeroth coordinate. -/
def coordinate (n : ℕ) : Fin (n + 1) → PolyRing R n :=
  Fin.cases (1 - ∑ j : Fin n, generator n j) (generator n)

end
end CentralPolynomialSimplex
end
