set_option warningAsError true

@[expose] public section

open Function

open scoped Matrix

namespace LinearMap

universe u

theorem mem_ker_coefficientRowScalarMap_iff_mem_ker_dotProductBilin
    (R : Type u) [CommRing R] {n : ℕ} (a x : Fin n → R) :
    x ∈ LinearMap.ker (Bass.coefficientRowScalarMap R n a) ↔
      x ∈ LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a) := by
  simp only [LinearMap.mem_ker, coefficientRowScalarMap_eq_dotProductBilin]

end LinearMap
end
