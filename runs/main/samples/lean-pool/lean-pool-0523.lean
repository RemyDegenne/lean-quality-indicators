@[expose] public section

namespace NRR.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem upperClosedHalfspace_convex (u : E) (t : ℝ) :
    Convex ℝ (upperClosedHalfspace u t) := by
  intro x hx y hy a b ha hb hab
  simp only [upperClosedHalfspace, Set.mem_ofPred_eq] at *
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  have ht : a * t + b * t = t := by rw [← add_mul, hab, one_mul]
  have h1 := mul_le_mul_of_nonneg_left hx ha
  have h2 := mul_le_mul_of_nonneg_left hy hb
  linarith

end NRR.Geometry
end
