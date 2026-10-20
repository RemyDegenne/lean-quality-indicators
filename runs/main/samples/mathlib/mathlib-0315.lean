public section

universe u v w

variable {α : Type u}

open Set

open scoped Pointwise

section Semiring

namespace Ideal

variable [Semiring α] (I : Ideal α) {a : α}

theorem eq_top_of_unit_mem (x y : α) (hx : x ∈ I) (h : y * x = 1) : I = ⊤ :=
  eq_top_iff.2 fun z _ =>
    calc
      z * y * x ∈ I := I.mul_mem_left _ hx
      _ = z * (y * x) := mul_assoc z y x
      _ = z := by rw [h, mul_one]

end Ideal
end Semiring
end
