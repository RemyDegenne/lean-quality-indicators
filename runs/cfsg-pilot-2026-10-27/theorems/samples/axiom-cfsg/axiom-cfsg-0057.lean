public section

namespace CFSG.RankThree.S4Free.Stell

open CFSG.Open CFSG.Quasithin CFSG.RankThree.GF2n.SzExplicit Subgroup

universe u

section Core

open SzNatural

open scoped commutatorElement IsMulCommutative

variable {n : ℕ}

theorem mem_seriesPow {P : Subgroup (Sz n)} {k i : ℕ}
    {v : Multiplicative (Fin k → Fin 4 → F n)} :
    v ∈ seriesPow P k i ↔ ∀ j, Multiplicative.toAdd v j ∈ series n P i :=
  Iff.rfl

end Core
end CFSG.RankThree.S4Free.Stell
end
