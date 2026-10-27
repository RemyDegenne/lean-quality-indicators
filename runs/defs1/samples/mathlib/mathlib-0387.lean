@[expose] public section

open Set

variable {ι : Type*} (M : ι → Type*) [∀ i, Monoid (M i)]

namespace Monoid.CoprodI

variable {M}

variable {N : Type*} [Monoid N]

namespace NeWord

open Word

/-- One can multiply an element from the left to a non-empty reduced word if it does not cancel
with the first element in the word. -/
def mulHead {i j : ι} (w : NeWord M i j) (x : M i) (hnotone : x * w.head ≠ 1) : NeWord M i j :=
  replaceHead (x * w.head) hnotone w

end NeWord
end Monoid.CoprodI
end
