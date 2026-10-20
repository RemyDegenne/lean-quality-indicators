@[expose] public section

variable {α β : Type*} {M N : Matroid α} {e f : α} {F X C I : Set α}

open Set

namespace Matroid

section IsColoop

variable {B K : Set α}

lemma IsColoop.mem_of_isBase (he : M.IsColoop e) (hB : M.IsBase B) : e ∈ B :=
  isColoop_iff_forall_mem_isBase.mp he hB

end IsColoop
end Matroid
end
