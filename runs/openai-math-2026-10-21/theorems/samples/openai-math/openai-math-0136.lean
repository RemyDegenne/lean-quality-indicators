namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ChainSuppression

open Function

open scoped Classical

variable {D : Type*} (σ τ : D → D)
    (hσ : Involutive σ) (hτ : Involutive τ)

include hσ hτ

variable [Finite D]

lemma length_pos (x : D) (hx : τ x=x) : 0 < length σ τ hσ hτ x hx :=
  (Nat.find_spec (exists_positive_return σ τ hσ hτ x hx)).1

end TorsionFreeZeroDivisors.ChainSuppression
end
end OAI
