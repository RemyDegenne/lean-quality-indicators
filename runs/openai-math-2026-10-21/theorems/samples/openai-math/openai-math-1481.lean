namespace OAI

universe u v

noncomputable section

open scoped BigOperators Classical

namespace Problem313.BiasedFourier

variable {ι : Type u} [Fintype ι]

theorem weight_mass_one (p : ℝ) : ∑ x : ι → Bool, weight p x = 1 := by
  unfold weight
  rw [← Fintype.prod_sum]
  simp [scalarWeight]

end Problem313.BiasedFourier
end
end OAI
