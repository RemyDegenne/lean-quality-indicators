@[expose] public section

open Function

namespace Set

variable {α β : Type*} {s t : Set α} {a b : α}

/-- Inserting an element to a set is equivalent to the option type. -/
def subtypeInsertEquivOption
    [DecidableEq α] {t : Set α} {x : α} (h : x ∉ t) :
    { i // i ∈ insert x t } ≃ Option { i // i ∈ t } where
  toFun y := if h : ↑y = x then none else some ⟨y, by grind⟩
  invFun y := (y.elim ⟨x, mem_insert _ _⟩) fun z => ⟨z, by grind⟩
  left_inv y := by grind
  right_inv := by rintro (_ | y) <;> grind

end Set
end
