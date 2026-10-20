@[expose] public section

set_option autoImplicit false

set_option relaxedAutoImplicit false

universe u

open scoped TensorProduct

namespace IsIdempotentElem

variable {K : Type u} [CommSemiring K] {e : K}

@[simp] theorem coalgebraSpan_counit_apply (he : IsIdempotentElem e)
    (d : Ideal.span ({e} : Set K)) : he.coalgebraSpan.counit d = (d : K) := rfl

end IsIdempotentElem
end
