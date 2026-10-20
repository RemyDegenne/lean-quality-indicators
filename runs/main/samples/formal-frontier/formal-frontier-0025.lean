@[expose] public section

universe uR uS uι

namespace ModuleCat.RightExtension

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

variable (f : R →+* S)

variable (ι : Type uι) [Fintype ι] [DecidableEq ι]

section IdealQuotient

variable {R : Type uR} [Ring R]

@[simp]
theorem idealQuotientRightFreeLinearEquiv_mk
    (I : Ideal R) [I.IsTwoSided] (x : ι → R) :
    idealQuotientRightFreeLinearEquiv ι I
        (Submodule.Quotient.mk
          (p := idealSubmodule (M := ι → R) I) x) =
      fun i ↦ Ideal.Quotient.mk I (x i) := by
  simp [idealQuotientRightFreeLinearEquiv]

end IdealQuotient
end ModuleCat.RightExtension
end
