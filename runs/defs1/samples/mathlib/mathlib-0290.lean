@[expose] public section

universe u v w w₁ w₂

section NilpotentModules

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (k : ℕ) (N : LieSubmodule R L M)

namespace LieModule

variable {M₂ : Type w₁} [AddCommGroup M₂] [Module R M₂] [LieRingModule L M₂] [LieModule R L M₂]

variable (R L M)

open LieAlgebra

/-- A Lie module is nilpotent if its lower central series reaches 0 (in a finite number of
steps). -/
@[mk_iff isNilpotent_iff_int]
class IsNilpotent : Prop where
  mk_int ::
  nilpotent_int : ∃ k, lowerCentralSeries ℤ L M k = ⊥

end LieModule
end NilpotentModules
end
