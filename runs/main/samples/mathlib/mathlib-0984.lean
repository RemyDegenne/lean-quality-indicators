@[expose] public section

variable {R : Type*} [CommRing R]

namespace Ideal

open Submodule Associates

open scoped nonZeroDivisors

variable [IsDomain R]

@[simp]
theorem associatesEquivIsPrincipal_apply (x : R) :
    associatesEquivIsPrincipal R (.mk x) = span {x} := rfl

end Ideal
end
