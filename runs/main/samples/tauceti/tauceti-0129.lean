public section

namespace TauCeti

universe u

section DivisionRing

variable {F : Type u} [DivisionRing F] [DecidableEq F] {n : ℕ}

section Rows

variable (L : List (Fin n → F))

theorem rowReduce_eq_zero_of_lt {q : Fin n × (Fin n → F)} (hq : q ∈ rowReduce L) {d : Fin n}
    (hd : d < q.1) : q.2 d = 0 :=
  (isRowReduceState_rowReduceAux_finRange L).eq_zero_of_lt q hq d hd

end Rows
end DivisionRing
end TauCeti
end
