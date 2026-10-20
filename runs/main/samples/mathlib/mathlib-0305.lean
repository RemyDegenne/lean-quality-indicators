public section

open Set

variable {F R S : Type*}

namespace Int

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

section LinearOrderedField

variable {k : Type*} [Field k] [LinearOrder k] [IsOrderedRing k] [FloorRing k] {a b : k}

lemma ceil_div_ceil_inv_sub_one (ha : 1 ≤ a) : ⌈⌈(a - 1)⁻¹⌉ / a⌉ = ⌈(a - 1)⁻¹⌉ := by
  obtain rfl | ha := ha.eq_or_lt
  · simp
  have : 0 < a - 1 := by linarith
  refine le_antisymm (ceil_le.2 <| div_le_self (by positivity) ha.le) <| ?_
  rw [le_ceil_iff, sub_lt_comm, div_eq_mul_inv, ← mul_one_sub,
    ← lt_div_iff₀ (sub_pos.2 <| inv_lt_one_of_one_lt₀ ha)]
  convert ceil_lt_add_one (R := k) _
  field

end LinearOrderedField
end Int
end
