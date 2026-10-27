public section

open Set

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {τ : PointedCone ℝ V} (hi : IsIntegralLattice i) (A : Finset (ToricRay τ))

section Generator

variable (hτ : IsToricCone i τ)

/-- The cone of the star subdivision of `τ` along the rays in `A` spanned by the generators
indexed by `S`. It is a cone of the star subdivision when `S` omits `some ρ` for some `ρ ∈ A`. -/
noncomputable def starSubdivisionCone (S : Set (Option (ToricRay τ))) : PointedCone ℝ V :=
  PointedCone.hull ℝ (i '' (starSubdivisionGenerator hi A hτ '' S))

end Generator
end TauCeti.Toric
end
