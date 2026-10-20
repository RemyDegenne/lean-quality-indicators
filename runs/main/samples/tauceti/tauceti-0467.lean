public section

namespace Finsupp

variable {n : ℕ} {M : Type*}

theorem toLex_cons_lt_toLex_cons_iff [Zero M] [LT M] {x y : M} {s t : Fin n →₀ M} :
    toLex (cons x s) < toLex (cons y t) ↔ x < y ∨ x = y ∧ toLex s < toLex t := by
  simp only [Lex.lt_iff, ofLex_toLex]
  exact Fin.pi_lex_lt_cons_cons (α := fun _ ↦ M) (s := fun {_} ↦ (· < ·))

end Finsupp
end
