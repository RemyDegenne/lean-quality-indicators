public section

open MeasureTheory Set Filter

open scoped Topology

noncomputable section

namespace CKN

open CKN.Foundation.Parabolic

theorem vlMoll_abs_integral (n : ℕ) : ∫ y, |vlMoll n y| = 1 := by
  have h : (fun y => |vlMoll n y|) = vlMoll n := by
    funext y
    exact abs_of_nonneg (CKN.mollifier_nonneg (d := 3) _ y)
  rw [h]
  exact CKN.mollifier_integral_one (d := 3) _

end CKN
end
end
