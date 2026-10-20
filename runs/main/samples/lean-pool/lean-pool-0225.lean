open scoped DirectSum HahnSeries NatOrdinal TensorProduct

universe v

namespace Berarducci

public noncomputable section

variable {K : Type v} [Field K]

@[simp]
theorem principalComponentTensorMap_tmul (alpha : NatOrdinal)
    (x : PrincipalComponent K alpha) (p : FiniteSupportRing (K := K)) :
    principalComponentTensorMap K alpha (x ⊗ₜ p) =
      HahnSeries.Nonpositive.degreeFiniteSupportResidueEquiv K p •
        principalComponentToHahnDegreeLayer K alpha x := by
  rw [principalComponentTensorMap, TensorProduct.lift.tmul]
  rfl

end
end Berarducci
