public section

namespace Real

open scoped Real

open Finset

theorem cos_eq_cos_iff {x y : ℝ} : cos x = cos y ↔ ∃ k : ℤ, y = 2 * k * π + x ∨ y = 2 * k * π - x :=
  mod_cast @Complex.cos_eq_cos_iff x y

end Real
end
