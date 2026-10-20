@[expose] public section

universe uι uR uS uM uN

namespace ModuleCat

section Pi

variable {ι : Type uι} (Ri : ι → Type uR) [∀ i, Ring (Ri i)]

variable (Mi : ∀ i, ModuleCat.{uM} (Ri i)ᵐᵒᵖ)

theorem piRightSingle_smul (a : ∀ i, Ri i) (i : ι) (x : Mi i) :
    piRightSingle Ri Mi i (MulOpposite.op (a i) • x) =
      MulOpposite.op a • piRightSingle Ri Mi i x := by
  classical
  apply (piRight_ext_iff Ri Mi _ _).2
  intro j
  by_cases h : j = i
  · subst j
    simp only [piRight_smul_apply, piRightSingle_apply_same]
  · simp only [piRight_smul_apply, piRightSingle_apply_ne Ri Mi i j h, smul_zero]

end Pi
end ModuleCat
end
