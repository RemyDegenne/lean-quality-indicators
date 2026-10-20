@[expose] public section

namespace Polynomial

open Filter

section Shift

variable {R : Type*} [CommRing R]

theorem eval_comp_X_sub_C_natCast (p : R[X]) {t e : ℕ} (h : e ≤ t) :
    (p.comp (X - C (e : R))).eval (t : R) = p.eval ((t - e : ℕ) : R) := by
  rw [eval_comp_X_sub_C, Nat.cast_sub h]

end Shift
end Polynomial
end
