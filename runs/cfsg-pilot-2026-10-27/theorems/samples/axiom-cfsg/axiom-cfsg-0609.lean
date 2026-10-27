public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.ShapeExclusion

open Subgroup

variable {G : Type*} [Group G]

namespace Config

variable {S : Subgroup G} {t x ρ : G} {k : ℕ}

theorem y_pow_four (h : Config S t x ρ k) : h.y ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, h.y_sq, ← pow_mul]
  exact h.x_pow_four

end Config
end CFSG.ComponentClassification.AschbacherKnownGroup.ShapeExclusion
end
