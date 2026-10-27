@[expose] public section

set_option warningAsError true

universe u v

namespace Matrix.DualNumberMixedCommutator

open Matrix.DualNumberKernels

variable {R : Type u} [CommRing R] {n : Type v} [Fintype n] [DecidableEq n]

/-- The inner infinitesimal native GL unit, embedded along outer constants. -/
def epsilonLiftGL (X : Matrix n n R) :
    Matrix.GeneralLinearGroup n (DualNumber (DualNumber R)) :=
  ⟨(liftMatrix X).map (algebraMap (DualNumber R) (DualNumber (DualNumber R))),
    (liftMatrix (-X)).map (algebraMap (DualNumber R) (DualNumber (DualNumber R))),
    by rw [← Matrix.map_mul, ← liftMatrix_add]
       simp,
    by rw [← Matrix.map_mul, ← liftMatrix_add]
       simp⟩

end Matrix.DualNumberMixedCommutator
end
