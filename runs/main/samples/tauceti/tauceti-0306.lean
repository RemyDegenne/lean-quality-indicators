public section

namespace TauCeti

@[simp]
theorem isIdempotentElem_intCast_iff {R : Type*} [NonAssocRing R] [CharZero R] {n : ℤ} :
    IsIdempotentElem (n : R) ↔ n = 0 ∨ n = 1 := by
  rw [← IsIdempotentElem.iff_eq_zero_or_one, IsIdempotentElem, IsIdempotentElem, ← Int.cast_mul,
    Int.cast_inj]

end TauCeti
end
