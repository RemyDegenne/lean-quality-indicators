public section

open Function Set

universe u

namespace IsIdempotentElem

section CommRing

variable {R : Type u} [CommRing R] {e : R}

@[simp]
lemma one_sub_smul_span (he : IsIdempotentElem e) (x : Ideal.span {e}) :
    (1 - e) • x = 0 := by
  rw [sub_smul, one_smul, he.smul_span, sub_self]

end CommRing
end IsIdempotentElem
end
