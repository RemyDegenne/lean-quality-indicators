@[expose] public section

universe uR uS uT uι uκ uν

open Function

open scoped Matrix

namespace Module

section SquareScalarExtension

variable (R : Type uR) [Semiring R]

variable (ι : Type uι) [Fintype ι]

variable [DecidableEq ι]

theorem rightEndomorphismScalarExtension_eq_rightFreeLinearMapScalarExtension
    {S : Type uS} [Semiring S] (f : R →+* S)
    (g : Module.End Rᵐᵒᵖ (ι → R)) :
    rightEndomorphismScalarExtension R ι f g =
      rightFreeLinearMapScalarExtension R ι ι f g := rfl

end SquareScalarExtension
end Module
end
