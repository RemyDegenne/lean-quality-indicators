public section

open MeasureTheory Set Filter

noncomputable section

namespace CKN

open CKN.Foundation.Parabolic

/-- The primitive from the convolved initial trace. -/
@[expose]
def vlPrim (a : ℝ) (k : Vec3 → ℝ) (w₀ : Vec3 → ℝ) (w : Vec3 × ℝ → ℝ)
    (H : Fin 3 → Vec3 × ℝ → ℝ) (f : Vec3 × ℝ → ℝ) (x : Vec3) (t : ℝ) : ℝ :=
  vlConv k w₀ x + ∫ s in a..t, vlSource k w H f x s

end CKN
end
end
