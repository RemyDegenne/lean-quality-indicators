public section

open Function Set

universe u

namespace IsIdempotentElem

section CommSemiring

variable {R : Type u} [CommSemiring R] {e : R}

theorem not_free_span (he : IsIdempotentElem e) (h0 : e ≠ 0) (h1 : e ≠ 1) :
    ¬ Module.Free R (Ideal.span {e}) :=
  fun hfree ↦ (he.free_span_iff.mp hfree).elim h0 h1

end CommSemiring
end IsIdempotentElem
end
