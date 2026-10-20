public section

namespace TauCeti

variable {α : Type*}

/-- A loop, read as a function on `ℕ`: past its last letter it is padded with the base letter. -/
def loopPathAt (a₀ : α) (bs : List (List α)) (i : ℕ) : α :=
  (loopPath a₀ bs).getD i a₀

end TauCeti
end
