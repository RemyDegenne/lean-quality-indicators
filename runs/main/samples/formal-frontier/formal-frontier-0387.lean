public section

open Function Set

universe u

namespace IsIdempotentElem

section Ring

variable {R : Type u} [Ring R] {e : R}

@[simp]
lemma spanProdEquiv_apply_right (he : IsIdempotentElem e) (x : Ideal.span {1 - e}) :
    he.spanProdEquiv (0, x) = (x : R) := by simp

end Ring
end IsIdempotentElem
end
