public section

open Matrix TauCeti

namespace Matrix.SpecialLinearGroup

universe u

noncomputable section

variable {R : Type u} {n : ℕ} [CommRing R]

/-- The determinant-one diagonal torus separates coordinates if each pair of distinct coordinates
receives different values under some diagonal element of determinant one. -/
def DiagonalTorusSeparatesCoordinates (R : Type u) [CommRing R] (n : ℕ) : Prop :=
  ∀ i j : Fin n, i ≠ j → ∃ t : Fin n → Rˣ, ∏ r, (t r : R) = 1 ∨ t i ≠ t j

end
end Matrix.SpecialLinearGroup
end
