public noncomputable section

open UpperHalfPlane MatrixGroups ModularForm Matrix.SpecialLinearGroup Filter Topology Function Set

open scoped Manifold MatrixGroups

namespace TauCeti.ModularForm

open ModularGroup

local notation "𝕢" => Function.Periodic.qParam

@[simp]
theorem meromorphicOrderAt_cuspFunction_j :
    _root_.meromorphicOrderAt (cuspFunction 1 j) 0 = -1 := by
  rw [_root_.meromorphicOrderAt_congr cuspFunction_j_eventuallyEq]
  exact TauCeti.Contour.meromorphicOrderAt_div_eq_neg_one
    analyticAt_cuspFunction_qParam_mul_j
    (by rw [cuspFunction_qParam_mul_j_zero]; exact one_ne_zero)
    (h := id) analyticAt_id rfl (by simp)

end TauCeti.ModularForm
end
