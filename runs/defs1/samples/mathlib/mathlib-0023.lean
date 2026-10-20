@[expose] public section

variable {M : Type*} [SeminormedCommGroup M]

variable (M) in
/-- The null subgroup with respect to the norm. -/
@[to_additive /-- The additive null subgroup with respect to the norm. -/]
def nullSubgroup : Subgroup M where
  carrier := {x : M | ‖x‖ = 0}
  mul_mem' {x y} (hx : ‖x‖ = 0) (hy : ‖y‖ = 0) := by
    apply le_antisymm _ (norm_nonneg' _)
    refine (norm_mul_le' x y).trans_eq ?_
    rw [hx, hy, add_zero]
  one_mem' := norm_one'
  inv_mem' {x} (hx : ‖x‖ = 0) := by simpa only [Set.mem_ofPred_eq, norm_inv'] using hx

end
