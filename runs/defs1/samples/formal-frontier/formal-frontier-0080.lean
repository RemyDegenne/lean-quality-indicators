@[expose] public section

set_option warningAsError true

universe u v

namespace Matrix.DualNumberMixedSLCommutator

open Matrix.DualNumberKernels Matrix.DualNumberMixedCommutator

variable {R : Type u} [CommRing R] {n : Type v} [Fintype n] [DecidableEq n]

/-- Outer-constant embedding of the native inner special-linear infinitesimal. -/
def epsilonLiftSL (X : LieAlgebra.SpecialLinear.sl n R) :
    Matrix.SpecialLinearGroup n (DualNumber (DualNumber R)) :=
  Matrix.SpecialLinearGroup.map
    (algebraMap (DualNumber R) (DualNumber (DualNumber R))) (liftSL X)

end Matrix.DualNumberMixedSLCommutator
end
