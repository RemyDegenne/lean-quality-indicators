public section

namespace CFSG.CGT.Foote82.Proof511

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem mul_eq_one_symm {B B' : M43} (h : B * B' = 1) : B' * B = 1 := by
  rw [← Matrix.inv_eq_right_inv h]
  exact Matrix.nonsing_inv_mul B (Matrix.isUnit_det_of_right_inverse h)

end CFSG.CGT.Foote82.Proof511
end
