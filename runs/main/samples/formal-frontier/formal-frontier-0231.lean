@[expose] public section

universe uι uκ uD

namespace KTheory

variable {ι : Type uι} (D : ι → Type uD) (κ : ι → Type uκ)

variable [∀ i, DivisionRing (D i)] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
  [∀ i, Nonempty (κ i)] [Finite ι]

namespace ProjectiveClass

theorem matrixFamilyEquiv_free (n : ℕ) (i : ι) :
    matrixFamilyEquiv D κ
        (of (∀ j, Matrix (κ j) (κ j) (D j))
          (Fin n → (∀ j, Matrix (κ j) (κ j) (D j))ᵐᵒᵖ)) i =
      n * Fintype.card (κ i) := by
  rw [of_fin_fun_eq_nsmul]
  have hregular := of_eq_of_equiv (∀ j, Matrix (κ j) (κ j) (D j))
    (∀ j, Matrix (κ j) (κ j) (D j))ᵐᵒᵖ
    (MulOpposite.opLinearEquiv (∀ j, Matrix (κ j) (κ j) (D j))ᵐᵒᵖ).symm
  rw [hregular, map_nsmul]
  change n • matrixFamilyEquiv D κ
    (of (∀ j, Matrix (κ j) (κ j) (D j))
      (∀ j, Matrix (κ j) (κ j) (D j))) i = _
  rw [matrixFamilyEquiv_regular, Nat.nsmul_eq_mul]

end ProjectiveClass
end KTheory
end
