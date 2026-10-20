@[expose] public section

universe uR uS uM

open scoped Pointwise

namespace ModuleCat.RightExtension

variable {R : Type uR} [Ring R]

section IdealQuotient

variable {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M]

@[simp]
theorem toIdealQuotient_tmul (I : Ideal R) [I.IsTwoSided] (m : M)
    (s : R ⧸ I) :
    toIdealQuotient (M := M) I (tmul (Ideal.Quotient.mk I) m s) =
      MulOpposite.op s •
        Submodule.Quotient.mk (p := idealSubmodule (M := M) I) m := by
  exact fromSemilinear_tmul _ _ _ _

end IdealQuotient
end ModuleCat.RightExtension
end
