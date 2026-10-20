@[expose] public section

universe uι uR uS uM uN

namespace ModuleCat

namespace RightExtension

section Pi

variable {ι : Type uι} (Ri : ι → Type uR) [∀ i, Ring (Ri i)]

theorem piLinearEquiv_symm_single_tmul [Finite ι]
    (M : ModuleCat.{uM} (∀ i, Ri i)ᵐᵒᵖ) (i : ι) (m : M) (r : Ri i) :
    (piLinearEquiv Ri M).symm
        (ModuleCat.piRightSingle Ri
          (fun j => ModuleCat.of (Ri j)ᵐᵒᵖ (Obj (Pi.evalRingHom Ri j) M))
          i (tmul (Pi.evalRingHom Ri i) m r)) =
      MulOpposite.op
        (@Pi.single ι Ri (fun _ => inferInstance) (Classical.decEq ι) i r) • m := by
  classical
  apply (piLinearEquiv Ri M).injective
  rw [LinearEquiv.apply_symm_apply]
  apply funext
  intro j
  rw [piLinearEquiv_apply, smul_tmul]
  by_cases h : j = i
  · subst j
    rw [ModuleCat.piRightSingle_apply_same]
    change tmul (Pi.evalRingHom Ri i) m r =
      tmul (Pi.evalRingHom Ri i) m ((Pi.single i r) i * 1)
    rw [Pi.single_eq_same, mul_one]
  · rw [ModuleCat.piRightSingle_apply_ne Ri
      (fun j => ModuleCat.of (Ri j)ᵐᵒᵖ (Obj (Pi.evalRingHom Ri j) M)) i j h]
    change 0 = tmul (Pi.evalRingHom Ri j) m ((Pi.single i r) j * 1)
    rw [Pi.single_eq_of_ne h, zero_mul]
    simp [tmul]

end Pi
end RightExtension
end ModuleCat
end
