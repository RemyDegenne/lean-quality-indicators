set_option warningAsError true

@[expose] public section

open scoped Matrix

namespace LinearEquiv

universe u v

@[simp]
theorem coefficientProductRowKernelEquiv_apply_val (R : Type u) [CommRing R]
    (P : Type v) [AddCommGroup P] [Module R P]
    (e : (Fin 2 → R) ≃ₗ[R] (R × P)) (p : P) :
    (coefficientProductRowKernelEquiv R P e p).1 = e.symm (0, p) := by
  rfl

end LinearEquiv
end
