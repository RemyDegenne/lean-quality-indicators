@[expose] public section

variable {R : Type*}

theorem IsStarProjection.two_mul_sub_one_mem_unitary {R : Type*} [Ring R] [StarRing R] {p : R}
    (hp : IsStarProjection p) : 2 * p - 1 ∈ unitary R := by
  simp only [two_mul, Unitary.mem_iff, star_sub, star_add,
    hp.isSelfAdjoint.star_eq, star_one, mul_sub, mul_add,
    sub_mul, add_mul, hp.isIdempotentElem.eq, one_mul, add_sub_cancel_right,
    mul_one, sub_sub_cancel, and_self]

end
