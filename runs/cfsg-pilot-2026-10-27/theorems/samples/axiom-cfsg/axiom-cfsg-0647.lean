public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.D

open CFSG.ClassicalInvolution.PhanB3.S.Std

variable {K : Type} [Field K] (M : Model K)

theorem bf_sum_sum (x : Fin 3 → K) (z : Fin 3 → Vec K) :
    bf M (∑ i, x i • z i) (∑ i, x i • z i) = ∑ i, ∑ j, bf M (z i) (z j) * (x i * x j) := by
  rw [bf_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [bf_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end CFSG.ClassicalInvolution.PhanB3.S.Std.D
end
