public noncomputable section

namespace CFSG.Monster.B.Classical.E6Adjoint

open CFSG.Blueprint.Chevalley

variable (R : Type*) [CommRing R]

variable {R}

theorem toVec_xor
    [CharP R 2] (m n : ℕ) : toVec R (m ^^^ n) = toVec R m + toVec R n := by
  simp only [toVec, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Nat.testBit_xor]
  cases m.testBit k <;> cases n.testBit k <;>
    simp [← Finsupp.single_add, one_add_one_eq_two, CharTwo.two_eq_zero]

end CFSG.Monster.B.Classical.E6Adjoint
end
