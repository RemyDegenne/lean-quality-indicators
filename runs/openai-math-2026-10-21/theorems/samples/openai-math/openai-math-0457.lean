namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem315.CrossCellMoments

variable {α β : Type*} [Fintype α] [Fintype β]

theorem average_product_independent_of_ne_two (s : ℕ) (hs : s ≠ 2)
    (r : α → Fin 3) (c : β → Fin 3) (f : α → ℝ) (g : β → ℝ) :
    average s r c (fun x y => f x * g y) =
      average s r c (fun x _ => f x) * average s r c (fun _ y => g y) := by
  have h := CrossBlock.countAverage_independent s hs
    (fun _ : α => 1) (fun _ : β => 1) r c f g
  rw [← average_product_eq_countAverage s r c f g,
    ← average_product_eq_countAverage s r c f (fun _ => 1),
    ← average_product_eq_countAverage s r c (fun _ => 1) g] at h
  simpa only [mul_one, one_mul] using h

end Problem315.CrossCellMoments
end
end OAI
