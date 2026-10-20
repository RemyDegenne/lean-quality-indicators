public section

open CKN

open MeasureTheory Set Filter

open scoped Interval Topology ENNReal

open CKN.Foundation.Parabolic

noncomputable section

namespace ESS.LPS

variable {a b : ℝ} {w r : Vec3 × ℝ → ℝ}

/-- The averaged constant of the mollified time primitive. -/
@[expose] def lpsPrimConst (a b : ℝ) (k : Vec3 → ℝ) (w r : Vec3 × ℝ → ℝ) (x : Vec3) : ℝ :=
  (b - a)⁻¹ * ∫ s in Ioo a b, (vlConvT k w x s - ∫ q in a..s, vlConvT k r x q)

end ESS.LPS
end
end
