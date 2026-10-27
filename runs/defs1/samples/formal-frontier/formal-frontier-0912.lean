@[expose] public section

universe uR uS uι

namespace ModuleCat.RightExtension

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

variable (f : R →+* S)

variable (ι : Type uι) [Fintype ι] [DecidableEq ι]

/-- Scalar extension of a finite canonical right-free module is the canonical
right-free module over the target ring. -/
noncomputable def rightFreeLinearEquiv :
    Obj f (ι → R) ≃ₗ[Sᵐᵒᵖ] (ι → S) :=
  LinearEquiv.ofLinearMap (rightFreeTo f ι) (rightFreeFrom f ι)
    (by
      apply LinearMap.ext
      intro x
      exact rightFreeTo_rightFreeFrom f ι x)
    (by
      apply LinearMap.ext
      intro z
      exact rightFreeFrom_rightFreeTo f ι z)

end ModuleCat.RightExtension
end
