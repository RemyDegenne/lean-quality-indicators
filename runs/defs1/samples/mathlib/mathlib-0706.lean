@[expose] public section

open List (Vector)

open Finset Function Sym

universe u

variable {α β γ : Type*}

notation3 "s(" x ", " y ")" => Sym2.mk x y

namespace Sym2

variable {z : Sym2 α} {f : α → β}

/-- A type `α` is naturally included in the diagonal of `α × α`, and this function gives the image
of this diagonal in `Sym2 α`.
-/
def diag (x : α) : Sym2 α := s(x, x)

end Sym2
end
