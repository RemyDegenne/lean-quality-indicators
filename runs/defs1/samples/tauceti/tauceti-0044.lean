open scoped Matrix

public section

namespace TauCeti.D4Tripled

open TauCeti.DynkinType

universe u

/-- The rational coordinate equivalence induced by triality from block two to block zero. -/
noncomputable def d4BlockTwoToZeroEquiv :
    (Block 2 → ℚ) ≃ₗ[ℚ] (Block 0 → ℚ) :=
  LinearEquiv.piCongrLeft' ℚ (fun _ => ℚ) d4BlockTwoToZeroIndexEquiv

end TauCeti.D4Tripled
end
