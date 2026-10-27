public section

namespace TauCeti

open LieAlgebra LieAlgebra.IsKilling LieModule

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

namespace IsChevalleySystem

variable {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : IsChevalleySystem ω x)

include hx

/-- The integral root--coroot Lie lattice canonically attached to a Chevalley system. -/
noncomputable def chevalleyLieLattice : LieSubalgebra ℤ L :=
  hx.toIsSl2System.rootCorootLieSubalgebra fun α β γ _ _ hγ hαβ =>
    hx.exists_int_lie_eq_smul α β γ hγ hαβ

end IsChevalleySystem
end TauCeti
end
