@[expose] public section

namespace LeanPool.ArtinWedderburn

variable {R : Type*} [Ring R]

open Pointwise Set

lemma both_mul_zero {a b x y : R} (hab : bothMul a b = {0}) (hx : x ∈ mulClosure a)
    (hy : y ∈ mulClosure b) : x * y = 0 := by
  obtain ⟨x1, x2, hx⟩ := hx
  obtain ⟨y1, y2, hy⟩ := hy
  have prod_in_both_mul : a * (x2 * y1) * b ∈ bothMul a b := ⟨x2 * y1, rfl⟩
  have prod_zero : a * (x2 * y1) * b = 0 := by
    simp_all
  rw [hx, hy]
  calc
    x1 * a * x2 * (y1 * b * y2) = x1 * (a * (x2 * y1) * b) * y2 := by noncomm_ring
    _ = 0 := by rw [prod_zero]; noncomm_ring

end LeanPool.ArtinWedderburn
end
