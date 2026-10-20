@[expose] public section

open Polynomial

namespace FrobeniusTwistedLine

open scoped TensorProduct

noncomputable section

variable (K : Type*) [Field K]

variable {K}

theorem SatisfiesEquation.map {A B : Type*} [Ring A] [Ring B]
    [Algebra K A] [Algebra K B] {p : ℕ} {t : K} {x y : A}
    (h : SatisfiesEquation p t x y) (f : A →ₐ[K] B) :
    SatisfiesEquation p t (f x) (f y) := by
  rw [SatisfiesEquation] at h ⊢
  rw [← map_pow, ← map_pow, ← f.commutes t, ← map_mul, ← map_sub, h, map_zero]

end
end FrobeniusTwistedLine
end
