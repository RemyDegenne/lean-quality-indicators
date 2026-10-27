@[expose] public section

universe u v

open CategoryTheory

namespace KTheory

variable (K : Type u) [DivisionRing K]

namespace ProjectiveClass

section DimensionEquivalence

/-- Dimension classifies finite projective right-module classes over a division
ring as an additive monoid. The forward map is the canonical dimension map. -/
@[no_expose]
noncomputable def finrankEquiv : ProjectiveClass K ≃+ ℕ :=
  AddEquiv.ofBijective (finrankHom K) (finrankHom_bijective K)

end DimensionEquivalence
end ProjectiveClass
end KTheory
end
