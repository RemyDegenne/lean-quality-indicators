public section

namespace TauCeti

open LieAlgebra LieModule Module

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]

variable {H}

variable (b : (IsKilling.rootSystem H).Base)

variable (H)

/-- The **negative nilradical** `n⁻ = ⨁_{α < 0} Lα` of the positive system determined by `b`. -/
noncomputable def negativeNilradical : LieSubalgebra K L :=
  rootSpaceSubalgebra H _ (isSpecialClosedRootSet_negRoots b)

end TauCeti
end
