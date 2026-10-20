@[expose] public section

namespace MooreBound

open Set

namespace DegreeDiameter

open SimpleGraph

universe u

variable {V : Type u}

@[simp] lemma bipartiteExpansion_adj_inr_inl (H : SimpleGraph V) (x y : V) :
    (bipartiteExpansion H).Adj (.inr y) (.inl x) ↔ Linked H x y :=
  Iff.rfl

end DegreeDiameter
end MooreBound
end
