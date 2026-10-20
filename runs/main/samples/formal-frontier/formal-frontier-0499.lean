set_option warningAsError true

@[expose] public section

open scoped Matrix

namespace LinearEquiv

universe u

@[simp]
theorem rightCoefficientKernelEquivOfMatrixInverse_symm_apply (R : Type u) [Ring R]
    {n m : ℕ} (a : Fin n → R)
    (A : Matrix (Fin (m + 1)) (Fin n) R)
    (B : Matrix (Fin n) (Fin (m + 1)) R)
    (hrow : A 0 = a) (hAB : A * B = 1) (hBA : B * A = 1)
    (y : Fin m → R) :
    ((rightCoefficientKernelEquivOfMatrixInverse R a A B hrow hAB hBA).symm y).1 =
      B *ᵥ Fin.cons 0 y := by
  rfl

end LinearEquiv
end
