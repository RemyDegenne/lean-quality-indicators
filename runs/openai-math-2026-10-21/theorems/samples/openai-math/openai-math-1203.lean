namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem337.CyclicSmoothing

lemma window_le_of_kernel_bound {G : Type*} [AddGroup G]
    (K : G → ℝ) (J : Finset G) (x : G) (η : ℝ)
    (h : ∀ y ∈ J, K (x - y) ≤ η) : window K J x ≤ (J.card : ℝ) * η := by
  calc
    window K J x ≤ ∑ _y ∈ J, η := Finset.sum_le_sum h
    _ = (J.card : ℝ) * η := by simp

end Problem337.CyclicSmoothing
end
end OAI
