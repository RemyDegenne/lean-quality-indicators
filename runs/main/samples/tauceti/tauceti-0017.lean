public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane

open scoped MatrixGroups ModularForm Pointwise

variable {N : ℕ}

open CongruenceSubgroup

@[simp]
theorem coe_cuspToModFormCharSpace (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (f : cuspFormCharSpace k χ) :
    (cuspToModFormCharSpace k χ f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      ((f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := (rfl)

end
