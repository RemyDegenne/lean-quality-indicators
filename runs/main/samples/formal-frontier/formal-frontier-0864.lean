set_option warningAsError true

@[expose] public section

open Function

open scoped Matrix

namespace Bass

universe u

theorem free_ker_coefficientRowConsMap_of_stableRangeCondition
    (R : Type u) [CommRing R] (n : ℕ)
    (hstable : StableRangeCondition R n) (a₀ : R) (a : Fin n → R)
    (ha : IsRightUnimodularCons a₀ a) :
    Module.Free R (LinearMap.ker (coefficientRowConsMap R n a₀ a)) :=
  Module.Free.of_equiv
    (coefficientRowConsKernelEquivOfStableRangeCondition
      R n hstable a₀ a ha).symm

end Bass
end
