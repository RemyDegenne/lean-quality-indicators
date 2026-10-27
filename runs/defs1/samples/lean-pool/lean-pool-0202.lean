open scoped MaxAddDegree

universe u

public noncomputable section

variable {R : Type u} [CommRing R]

/-- A decreasing multiplicative filtration by ideals, separated in the sense that every nonzero
element eventually leaves it. -/
structure IsSeparatedFiltration (F : ℕ → Ideal R) : Prop where
  /-- The filtration is decreasing. -/
  antitone : Antitone F
  /-- The zeroth stage is everything. -/
  top : F 0 = ⊤
  /-- The filtration is multiplicative: `F a · F b ⊆ F (a + b)`. -/
  mul_le : ∀ a b, F a * F b ≤ F (a + b)
  /-- Every nonzero element eventually leaves the filtration. -/
  exists_not_mem : ∀ {x : R}, x ≠ 0 → ∃ j, x ∉ F j

end
