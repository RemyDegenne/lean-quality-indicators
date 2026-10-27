public section

namespace CFSG.StandardType

open CFSG.Assembly TableB TypeA TwoThree

namespace TwoThree

section B2der

variable {K : Type} [Field K] [Finite K]

theorem not_dvd_card_GL_four (hK : Nat.card K = 2) : ¬ 3 ^ 3 ∣ Nat.card (GL (Fin 2 ⊕ Fin 2) K) := by
  rw [card_GL_four hK]
  norm_num

end B2der
end TwoThree
end CFSG.StandardType
end
