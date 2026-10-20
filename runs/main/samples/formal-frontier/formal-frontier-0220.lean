@[expose] public section

open CategoryTheory

namespace CategoryTheory.QuadrantProductTotal

universe u

variable {R : Type u} [Ring R]

theorem differential_apply_pos (K : Bicomplex R) (k : ℤ)
    (x : Product K k) (i : Diag (k - 1)) (hi : 0 < i.1.1) :
    differential K k x i =
      (K.X i.1.1).d (i.1.2 + 1) i.1.2 (x (horizontalIndex i)) +
        (Int.negOnePow (k + 1) : ℤ) •
          (K.d (i.1.1 - 1) i.1.1).f i.1.2 (x (verticalIndex i hi)) := by
  simp [differential, horizontal, vertical, hi]
  rfl

end CategoryTheory.QuadrantProductTotal
end
