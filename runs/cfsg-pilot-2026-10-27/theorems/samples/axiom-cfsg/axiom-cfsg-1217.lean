public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearThreeFourOuter

open LinearFlag

open Matrix

variable {k : Type*} [Field k]

section Sigma

variable {σ : k ≃+* k} (hσ : ∀ a, σ a = a ^ 2)

include hσ

theorem sigma_mul_self (hk : Nat.card k = 4) : σ * σ = 1 := by
  refine RingEquiv.ext fun a => ?_
  change σ (σ a) = a
  rw [hσ, hσ, ← pow_mul]
  exact LinearFieldFour.pow_four_eq_self hk a

end Sigma
end LinearThreeFourOuter
end CFSG.LocalAnalysis.ComponentInitial
end
