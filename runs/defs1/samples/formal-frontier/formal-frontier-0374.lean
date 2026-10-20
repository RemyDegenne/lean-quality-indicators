set_option warningAsError true

@[expose] public section

open Function

open scoped Matrix

namespace Bass

universe u

/-- The linear functional represented by a finite coefficient row. -/
def coefficientRowLinearMap (R : Type u) [CommRing R]
    (n : ℕ) (a : Fin n → R) :
    (Fin n → R) →ₗ[R] (Fin 1 → R) :=
  (coefficientRowMatrix R n a).mulVecLin

end Bass
end
