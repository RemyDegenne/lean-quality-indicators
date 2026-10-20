universe v w w'

open scoped DirectSum HahnSeries NatOrdinal TensorProduct

public noncomputable section

namespace Berarducci

open Berarducci

open HahnSeries.Nonpositive

variable {K : Type v} {E : Type w} [Field K] [Field E]

section Layer

theorem principalSubringBaseChangeLinear_tmul [Algebra K E]
    (e : E) (A : PrincipalSubring K) :
    principalSubringBaseChangeLinear K E (e ⊗ₜ[K] A) =
      e • principalSubringCoefficientExtend K E A := by
  induction A using DirectSum.induction_on with
  | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero, smul_zero]
  | of alpha A =>
      rw [principalSubringBaseChangeLinear_tmul_of,
        principalSubringCoefficientExtend_of]
  | add x y hx hy => rw [TensorProduct.tmul_add, map_add, hx, hy, map_add, smul_add]

end Layer
end Berarducci
end
