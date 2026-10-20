@[expose] public section

variable {α : Type*}

namespace Ordset

open Ordnode

variable [Preorder α]

/-- O(1). Is the set empty? -/
def Empty (s : Ordset α) : Prop :=
  s = ∅

end Ordset
end
