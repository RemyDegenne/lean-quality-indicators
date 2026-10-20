public section

namespace Polynomial

variable {R : Type*} {r : R}

section CommRing

variable [CommRing R] {P : R[X]}

lemma isUnit_iff' :
    IsUnit P ↔ IsUnit (eval 0 P) ∧ IsNilpotent (P /ₘ X) := by
  suffices P = C (eval 0 P) + X * (P /ₘ X) by
    conv_lhs => rw [this]; simp
  conv_lhs => rw [← modByMonic_add_div P X]
  simp [modByMonic_X]

end CommRing
end Polynomial
end
