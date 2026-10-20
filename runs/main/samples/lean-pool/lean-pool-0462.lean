@[expose] public section

noncomputable section

open MeasureTheory

open Homogenization

namespace AVenhance.FaaDiBruno

theorem Product.harmonicOne_sq_le (m : ℕ) :
    Product.harmonicOne m ^ 2 ≤ (m : ℝ) * Product.harmonicTwo m := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range m)
    (fun _ : ℕ ↦ (1 : ℝ)) (fun k ↦ (k + 1 : ℝ)⁻¹)
  simpa [Product.harmonicOne, Product.harmonicTwo] using hc

end AVenhance.FaaDiBruno
end
end
