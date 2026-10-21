namespace OAI

noncomputable section

open scoped Pointwise

open scoped commutatorElement

namespace RingExchange

variable {R : Type*} [Ring R]

namespace Data

variable (D : Data R)

lemma aa : D.a*D.a=0 := by
  calc D.a*D.a=(D.a*D.E)*D.a := by rw [D.aE]
       _ = 0 := by rw [mul_assoc,D.Ea,mul_zero]

end Data
end RingExchange
end
end OAI
