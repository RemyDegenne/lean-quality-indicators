public section

namespace HeckeRing.GL2

open HeckeRing.GLn

variable (p : ℕ)

/-- **An entry assignment at `n = 2` is a single coordinate.** `UpperTriEntries 2 a` is a
dependent function on the ordered index pairs, and by `uniqueIndexPair` there is only the pair
`(0, 1)`; the fibre over it is `Fin (a 1 / a 0)`.

The fibre over `default` reduces to the fibre over `(0, 1)`, namely `Fin (a 1 / a 0)`, because
`default` is the field of `uniqueIndexPair`. The specialisation to `a = ![1, p]` is a separate
matter: it leaves the bound `p / 1`, and `finCongr (by simp)` transports along the
*propositional* equality `p / 1 = p`. -/
def upperTriEntriesEquiv (a : Fin 2 → ℕ) : UpperTriEntries 2 a ≃ Fin (a 1 / a 0) :=
  Equiv.piUnique _

end HeckeRing.GL2
end
