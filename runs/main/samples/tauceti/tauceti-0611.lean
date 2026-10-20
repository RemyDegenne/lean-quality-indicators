public section

open Finsupp Function

open scoped BigOperators

namespace TauCeti.KnotTheory

variable {R : Type*} [CommRing R] {N n : ℕ}

theorem jimboWeight_def (q : Rˣ) (a : Fin N) :
    jimboWeight q a = ↑(q ^ ((N : ℤ) - 1 - 2 * (a : ℕ))) := (rfl)

end TauCeti.KnotTheory
end
