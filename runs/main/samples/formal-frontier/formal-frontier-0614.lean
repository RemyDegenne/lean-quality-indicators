@[expose] public section

universe uR uS uT uι uκ uν

open Function

open scoped Matrix

namespace Module

section RingSquareCompatibility

variable (R : Type uR) [Ring R]

variable (ι : Type uι) [Fintype ι] [DecidableEq ι]

@[simp]
theorem rightEndomorphismLinearEquivOfMapMatrixQuotientIsUnit_apply
    (I : TwoSidedIdeal R) (hI : I.IsQuasiregular)
    (f : Module.End Rᵐᵒᵖ (ι → R))
    (hf : IsUnit ((Ideal.Quotient.mk I.asIdeal).mapMatrix
      (rightEndomorphismMatrixEquiv R ι f))) (x : ι → R) :
    rightEndomorphismLinearEquivOfMapMatrixQuotientIsUnit R ι I hI f hf x =
      f x :=
  rfl

end RingSquareCompatibility
end Module
end
