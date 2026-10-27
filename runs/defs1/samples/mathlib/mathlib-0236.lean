@[expose] public section

open Metric NNReal

namespace IsUltrametricDist

section Group

variable {S S' : Type*} [SeminormedGroup S] [SeminormedGroup S'] [IsUltrametricDist S]

section nonarch

variable (S)

/--
In a group with an ultrametric norm, closed balls around 1 of positive radius are open subgroups.
-/
@[to_additive /-- In an additive group with an ultrametric norm, closed balls around 0 of positive
radius are open subgroups. -/]
def closedBall_openSubgroup {r : ℝ} (hr : 0 < r) : OpenSubgroup S where
  carrier := Metric.closedBall (1 : S) r
  mul_mem' {x} {y} hx hy := by
    simp only [Metric.mem_closedBall, dist_eq_norm_inv_mul', inv_one, one_mul] at hx hy ⊢
    exact (norm_mul_le_max x y).trans (max_le hx hy)
  one_mem' := Metric.mem_closedBall_self hr.le
  inv_mem' := by simp only [mem_closedBall, dist_one_right, norm_inv', imp_self, implies_true]
  isOpen' := IsUltrametricDist.isOpen_closedBall _ hr.ne'

end nonarch
end Group
end IsUltrametricDist
end
