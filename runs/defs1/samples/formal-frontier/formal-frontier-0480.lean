@[expose] public section

open CategoryTheory

universe u v

namespace CentralPolynomialSimplex

noncomputable section

variable {R : Type u} [Ring R]

/-- The ring homomorphism induced by an ordinal map `alpha : [m] → [n]`.
It points from degree `n` to degree `m`. -/
def ordinalMap {m n : ℕ} (alpha : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    PolyRing R n →+* PolyRing R m :=
  substitute n (coefficient m) (fun j =>
    ⟨fiberValue alpha j.succ, fiber_mem_center alpha j.succ⟩)

end
end CentralPolynomialSimplex
end
