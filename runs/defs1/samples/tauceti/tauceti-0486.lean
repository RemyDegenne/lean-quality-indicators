open scoped Matrix

public section

namespace TauCeti.D4Tripled

open TauCeti.DynkinType

universe u

/-- The rational coordinate equivalence induced by triality from block zero to block one. -/
noncomputable def d4BlockZeroToOneEquiv :
    (Block 0 → ℚ) ≃ₗ[ℚ] (Block 1 → ℚ) :=
  LinearEquiv.piCongrLeft' ℚ (fun _ => ℚ) d4BlockZeroToOneIndexEquiv

end TauCeti.D4Tripled
end
