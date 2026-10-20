public section

open MeasureTheory Set Filter

noncomputable section

namespace CKN

open CKN.Foundation.Parabolic

theorem vlConv_apply_swap (k h : Vec3 → ℝ) (x : Vec3) :
    vlConv k h x = ∫ y, h y * k (x - y) := by
  rw [vlConv, convolution_eq_swap]
  simp [mul_comm]

end CKN
end
end
