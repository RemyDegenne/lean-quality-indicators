@[expose] public section

namespace EGZ.DecompositionParameters

open scoped BigOperators

@[simp] theorem scale_zero (d : ℕ) (δ₀ : ℝ) : scale d δ₀ 0 = δ₀ := by
  simp [scale]

end EGZ.DecompositionParameters
end
