@[expose] public section

universe uR uM uM' uM'' uN uN' uN'' uI uP uL

namespace BalancedTensorProduct

variable {R : Type uR} [Ring R]

variable {M : Type uM} {M' : Type uM'} {M'' : Type uM''}

variable {N : Type uN} {N' : Type uN'} {N'' : Type uN''}

variable [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M'']

variable [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']

variable [Module Rᵐᵒᵖ M] [Module Rᵐᵒᵖ M'] [Module Rᵐᵒᵖ M'']

variable [Module R N] [Module R N'] [Module R N'']

section Free

variable {ι : Type uI}

/-- A balanced tensor with a free right module is the finitely supported
family of its coordinates. -/
noncomputable def freeAddEquiv :
    BalancedTensorProduct R (ι →₀ Rᵐᵒᵖ) N ≃+ (ι →₀ N) where
  toFun := freeToFinsupp
  invFun := finsuppToFree
  map_add' := map_add _
  left_inv z := by
    induction z using induction_on with
    | zero => simp
    | pure x n => exact finsuppToFree_freeToFinsupp_tmul x n
    | neg z hz => simpa using congrArg Neg.neg hz
    | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
  right_inv x := by
    induction x using Finsupp.induction with
    | zero => simp
    | single_add i n x hin hn ih =>
        rw [map_add, map_add, finsuppToFree_single, freeToFinsupp_single_tmul, ih]
        simp

end Free
end BalancedTensorProduct
end
