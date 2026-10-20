@[expose] public section

set_option warningAsError true

universe u v

namespace Matrix.DualNumberMixedCommutator

open Matrix.DualNumberKernels

variable {R : Type u} [CommRing R] {n : Type v} [Fintype n] [DecidableEq n]

@[simp] theorem epsilonLiftGL_val (X : Matrix n n R) :
    (epsilonLiftGL X : Matrix n n (DualNumber (DualNumber R))) =
      (liftMatrix X).map (algebraMap (DualNumber R) (DualNumber (DualNumber R))) := rfl

end Matrix.DualNumberMixedCommutator
end
