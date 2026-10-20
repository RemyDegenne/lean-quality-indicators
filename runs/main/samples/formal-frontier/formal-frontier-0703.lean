@[expose] public section

set_option warningAsError true

universe u v w

namespace Matrix.DualNumberKernels

variable {R : Type u} [CommRing R] {n : Type v} [Fintype n] [DecidableEq n]

attribute [local instance 100] LieRing.ofAssociativeRing

@[simp] theorem slAdjoint_val (g : Matrix.GeneralLinearGroup n R)
    (X : LieAlgebra.SpecialLinear.sl n R) :
    ((slAdjoint g X).1 : Matrix n n R) =
      (g : Matrix n n R) * X.1 * (g⁻¹ : Matrix.GeneralLinearGroup n R) := by
  simp [slAdjoint, Matrix.lieConj_apply, Matrix.coe_units_inv]

end Matrix.DualNumberKernels
end
