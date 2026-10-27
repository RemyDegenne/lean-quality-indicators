public section

open Function Set

universe u

namespace IsIdempotentElem

section Semiring

variable {R : Type u} [Semiring R] {e : R}

/-- Right multiplication by `e` with codomain the canonical principal left
ideal. Idempotence is not needed to define this linear map. -/
@[expose] noncomputable def spanProjection (e : R) :
    R →ₗ[R] Ideal.span {e} :=
  (LinearMap.toSpanSingleton R R e).codRestrict (Ideal.span {e}) fun r ↦ by
    rw [LinearMap.toSpanSingleton_apply, smul_eq_mul]
    exact Ideal.mem_span_singleton'.2 ⟨r, rfl⟩

end Semiring
end IsIdempotentElem
end
