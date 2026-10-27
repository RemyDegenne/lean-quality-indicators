set_option warningAsError true

@[expose] public section

open Function

open scoped Matrix

namespace LinearEquiv

universe u

/-- The split kernel of a right coefficient row, with a specified right-inverse
column. The second inverse coordinate is the original row functional. -/
noncomputable def rightCoefficientKernelProd (R : Type u) [Ring R] {n : ℕ}
    (a b : Fin n → R) (hb : dotProductBilin R Rᵐᵒᵖ a b = 1) :
    (LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a) × R) ≃ₗ[Rᵐᵒᵖ]
      (Fin n → R) :=
  LinearMap.kerProdEquivOfRightInverse
    (dotProductBilin R Rᵐᵒᵖ a) (LinearMap.rightCoefficientSection R b)
    (LinearMap.rightCoefficientRow_comp_section R a b hb)

end LinearEquiv
end
