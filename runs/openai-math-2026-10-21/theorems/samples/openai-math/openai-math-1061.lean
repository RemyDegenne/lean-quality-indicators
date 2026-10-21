namespace OAI

namespace KadisonKastler

open UnitalTomsWinter Filter

open scoped TensorProduct Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

@[simp] theorem countableOperatorEntry_diagonal_mul
    (a : H →L[ℂ] H) (S : CountableHilbertSum H →L[ℂ] CountableHilbertSum H) (i j : ℕ) :
    countableOperatorEntry (l2Diagonal a * S) i j = a * countableOperatorEntry S i j := by
  ext x
  rfl

end
end KadisonKastler
end OAI
