namespace OAI

universe uE uF uR uS uV uΩ

noncomputable section

open MeasureTheory

open scoped BigOperators InnerProductSpace

namespace ClassicalON

open scoped Matrix

lemma moment4_plane_even (f g h k : ℝ) :
    moment4Plane f g h k + moment4Plane f (-g) h (-k) =
      (6 * (f*k-g*h)^2) • third^2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [third, pow_two, Matrix.cons_val_two]

end ClassicalON
end
end OAI
