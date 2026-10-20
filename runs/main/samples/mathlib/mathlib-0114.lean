public section

open Function

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

namespace Finset

section CommMonoid

variable [CommMonoid M] {f g : ι → M}

variable (f s)

variable {f s}

@[to_additive]
theorem prod_range_succ_comm (f : ℕ → M) (n : ℕ) :
    (∏ x ∈ range (n + 1), f x) = f n * ∏ x ∈ range n, f x := by
  rw [range_add_one, prod_insert notMem_range_self]

end CommMonoid
end Finset
end
