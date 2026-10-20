@[expose] public section

variable {R : Type*}

namespace Polynomial

section Field

variable [Field R] {f g : R[X]}

theorem Splits.of_natDegree_eq_two {x : R} (h₁ : f.natDegree = 2) (h₂ : f.eval x = 0) :
    Splits f := by
  have h : (f /ₘ (X - C x)).natDegree = 1 := by
    rw [natDegree_divByMonic f (monic_X_sub_C x), h₁, natDegree_X_sub_C]
  rw [← mul_divByMonic_eq_iff_isRoot.mpr h₂, splits_mul (X_sub_C_ne_zero x) (by aesop)]
  exact ⟨Splits.X_sub_C x, Splits.of_natDegree_eq_one h⟩

end Field
end Polynomial
end
