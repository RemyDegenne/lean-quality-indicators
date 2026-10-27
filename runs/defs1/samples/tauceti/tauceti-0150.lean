public section

namespace TauCeti

open List

variable {α : Type*} [LinearOrder α]

/-- The index of the row in which `TauCeti.rowInsert x T` adds its new cell. -/
def rowInsertIndex (x : α) : List (List α) → ℕ
  | [] => 0
  | row :: rows => (rowBump x row).2.elim 0 (rowInsertIndex · rows + 1)

end TauCeti
end
