public section

open Function Set

universe u

namespace IsIdempotentElem

section Ring

variable {R : Type u} [Ring R] {e : R}

/-- Complementary idempotent left ideals sum to the ring. The inverse uses
right multiplication by `e` and `1 - e`; neither idempotent need be central. -/
@[expose] noncomputable def spanProdEquiv (he : IsIdempotentElem e) :
    (Ideal.span {e} × Ideal.span {1 - e}) ≃ₗ[R] R where
  toFun x := x.1.1 + x.2.1
  invFun r := (spanProjection e r, spanProjection (1 - e) r)
  left_inv x := by
    apply Prod.ext
    · change spanProjection e ((x.1 : R) + (x.2 : R)) = x.1
      rw [map_add, he.spanProjection_apply_coe]
      have hzero : spanProjection e (x.2 : R) = 0 := by
        apply Subtype.ext
        obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 x.2.property
        simp only [spanProjection_apply, Submodule.coe_zero]
        rw [← ha, mul_assoc, he.one_sub_mul_self, mul_zero]
      rw [hzero, add_zero]
    · change spanProjection (1 - e) ((x.1 : R) + (x.2 : R)) = x.2
      rw [map_add, he.one_sub.spanProjection_apply_coe]
      have hzero : spanProjection (1 - e) (x.1 : R) = 0 := by
        apply Subtype.ext
        obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 x.1.property
        simp only [spanProjection_apply, Submodule.coe_zero]
        rw [← ha, mul_assoc, he.mul_one_sub_self, mul_zero]
      rw [hzero, zero_add]
  right_inv r := by
    change (spanProjection e r : R) + (spanProjection (1 - e) r : R) = r
    rw [spanProjection_apply, spanProjection_apply, ← mul_add, add_sub_cancel, mul_one]
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add]; abel
  map_smul' r x := by simp [mul_add]

end Ring
end IsIdempotentElem
end
