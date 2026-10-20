set_option warningAsError true

@[expose] public section

open Function

open scoped Matrix

namespace Bass

universe u

/-- A split coefficient row, with its leading coordinate separated from its
tail. -/
def coefficientRowConsMap (R : Type u) [CommRing R]
    (n : ℕ) (a₀ : R) (a : Fin n → R) :
    (R × (Fin n → R)) →ₗ[R] R :=
  (LinearMap.lsmul R R a₀).comp (LinearMap.fst R R (Fin n → R)) +
    (coefficientRowScalarMap R n a).comp (LinearMap.snd R R (Fin n → R))

end Bass
end
