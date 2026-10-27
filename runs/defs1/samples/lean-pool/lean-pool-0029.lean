@[expose] public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The union of the first `k` members of a family of graphs. -/
def unionFamily (H : ℕ → SimpleGraph V) (k : ℕ) : SimpleGraph V where
  Adj x y := ∃ i, i < k ∧ (H i).Adj x y
  symm := ⟨by
    rintro x y ⟨i, hi, hadj⟩
    exact ⟨i, hi, hadj.symm⟩⟩
  loopless := ⟨by
    rintro x ⟨i, -, hadj⟩
    exact (H i).irrefl hadj⟩

end Nibble.AX1
end
