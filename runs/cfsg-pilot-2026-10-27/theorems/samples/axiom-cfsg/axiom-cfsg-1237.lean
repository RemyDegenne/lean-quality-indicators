public section

namespace CFSG.RankThree.Classical.SteinbergBY

open Matrix CFSG.RankThree.Classical2

open scoped MatrixGroups commutatorElement

section Helpers

variable {Ω : Type*} [Field Ω]

local notation "M₃" => Matrix (Fin 3) (Fin 3) Ω

theorem inv_mul_coe_eq_scalar {X X' : SL(3, Ω)} {c : Ω} (h : (X' : M₃) = c • (X : M₃)) :
    ((X⁻¹ * X' : SL(3, Ω)) : M₃) = scalar (Fin 3) c := by
  rw [Matrix.SpecialLinearGroup.coe_mul, h, Matrix.mul_smul, ← Matrix.SpecialLinearGroup.coe_mul,
    inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, scalar_three_eq_smul]

end Helpers
end CFSG.RankThree.Classical.SteinbergBY
end
