set_option warningAsError true

@[expose] public section

open scoped Matrix

namespace CountableEndomorphism

universe u v

variable (S : Type u) (M : Type v) [Semiring S] [AddCommGroup M] [Module S M]

theorem free_kernel :
    Module.Free (Module.End S (ℕ →₀ M))ᵐᵒᵖ
      (LinearMap.ker
        (dotProductBilin (Module.End S (ℕ →₀ M)) (Module.End S (ℕ →₀ M))ᵐᵒᵖ
          (row S M))) := by
  have h := (Matrix.isRightUnimodular_and_free_kernel_iff_exists_rectangular_inverse
    (Module.End S (ℕ →₀ M)) (row S M)).mpr
      ⟨1, rectangularRow S M, rectangularColumn S M,
        rectangularRow_first S M, rectangularRow_mul_rectangularColumn S M,
        rectangularColumn_mul_rectangularRow S M⟩
  exact h.2

end CountableEndomorphism
end
