public section

namespace CFSG.OddTranspositions.QZ

open Equiv

theorem A5_involutions_conj : ∀ x y : alternatingGroup (Fin 5), x * x = 1 → x ≠ 1 → y * y = 1 →
    y ≠ 1 → ∃ h : alternatingGroup (Fin 5), h * x * h⁻¹ = y := by
  decide +kernel

end CFSG.OddTranspositions.QZ
end
