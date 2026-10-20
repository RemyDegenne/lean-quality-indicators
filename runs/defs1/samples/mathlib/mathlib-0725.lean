@[expose] public section

namespace Matrix

universe u

variable {α : Type u}

syntax (name := vecNotation) "![" term,* "]" : term

macro_rules
  | `(![$term:term, $terms:term,*]) => `(vecCons $term ![$terms,*])
  | `(![$term:term]) => `(vecCons $term ![])
  | `(![]) => `(vecEmpty)

variable {m n o : ℕ}

section Val

/-- `vecAlt0 v` gives a vector with half the length of `v`, with
only alternate elements (even-numbered). -/
def vecAlt0 (hm : m = n + n) (v : Fin m → α) (k : Fin n) : α := v ⟨(k : ℕ) + k, by lia⟩

end Val
end Matrix
end
