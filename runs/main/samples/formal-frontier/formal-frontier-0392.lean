set_option warningAsError true

@[expose] public section

open Function

open scoped Matrix

namespace LinearMap

universe u

theorem coefficientRowScalarMap_eq_dotProductBilin
    (R : Type u) [CommRing R] {n : ℕ} (a x : Fin n → R) :
    Bass.coefficientRowScalarMap R n a x = dotProductBilin R Rᵐᵒᵖ a x := by
  rfl

end LinearMap
end
