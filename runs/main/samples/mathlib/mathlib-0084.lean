@[expose] public section

variable {𝕜 E F G ι : Type*} {M : ι → Type*}

open Function Module Set

open scoped Pointwise Convex

open scoped Convex

section LinearOrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {x y z : 𝕜}

theorem Icc_subset_segment : Icc x y ⊆ [x -[𝕜] y] := by
  rintro z ⟨hxz, hyz⟩
  obtain rfl | h := (hxz.trans hyz).eq_or_lt
  · rw [segment_same]
    exact hyz.antisymm hxz
  rw [← sub_nonneg] at hxz hyz
  rw [← sub_pos] at h
  refine ⟨(y - z) / (y - x), (z - x) / (y - x), div_nonneg hyz h.le, div_nonneg hxz h.le, ?_, ?_⟩
  · rw [← add_div, sub_add_sub_cancel, div_self h.ne']
  · rw [smul_eq_mul, smul_eq_mul, ← mul_div_right_comm, ← mul_div_right_comm, ← add_div,
      div_eq_iff h.ne', add_comm, sub_mul, sub_mul, mul_comm x, sub_add_sub_cancel, mul_sub]

end LinearOrderedField
end
