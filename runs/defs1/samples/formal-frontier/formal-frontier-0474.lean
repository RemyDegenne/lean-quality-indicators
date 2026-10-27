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

/-- The balanced map used by `freeToFinsupp`. -/
noncomputable def freeBalancedMap :
    BalancedMap (R := R) (M := ι →₀ Rᵐᵒᵖ) (N := N) (ι →₀ N) where
  toFun x n := Finsupp.liftAddHom (fun i ↦ freeCoefficient i n) x
  map_zero_left n := by simp
  map_add_left x y n := by simp
  map_zero_right x := by simp [freeCoefficient]
  map_add_right x n₁ n₂ := by simp [freeCoefficient, smul_add]
  balance r x n := by
    simp only [Finsupp.liftAddHom_apply]
    rw [Finsupp.sum_smul_index']
    · apply Finsupp.sum_congr
      intro i hi
      simp [freeCoefficient, mul_smul]
    · intro i
      simp [freeCoefficient]

end Free
end BalancedTensorProduct
end
