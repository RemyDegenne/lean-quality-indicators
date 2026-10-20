public section

open Module QuadraticMap

open scoped Quaternion

namespace TauCeti

@[simp]
theorem realCliffordOneOneEquivMatrix_ι (v : Fin (1 + 1) → ℝ) :
    realCliffordOneOneEquivMatrix (CliffordAlgebra.ι _ v) = !![v 0, v 1; -v 1, -v 0] := by
  simp only [realCliffordOneOneEquivMatrix, AlgEquiv.trans_apply,
    CliffordAlgebra.equivOfIsometry_apply, CliffordAlgebra.map_apply_ι,
    IsometryEquiv.toIsometry_apply, realCliffordOneOneIsometry_apply,
    CliffordAlgebraQuaternion.equiv_apply, CliffordAlgebraQuaternion.toQuaternion_ι,
    QuaternionAlgebra.oneEquivMatrix_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end TauCeti
end
