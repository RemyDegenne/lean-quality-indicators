public section

namespace TauCeti

open Finset

namespace OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n)

@[simp]
theorem rotate_rotate : G.rotate.rotate = G :=
  Subtype.ext G.1.rotate_rotate

end OddComponentGridDiagram
end TauCeti
end
