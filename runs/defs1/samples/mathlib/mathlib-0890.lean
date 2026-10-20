@[expose] public section

open Module Function Set

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieModule

section

variable {M}

variable [LieRing.IsNilpotent L]

variable [HasUniqueDiv R] [IsDomain R] [IsTorsionFree R M] [IsNoetherian R M]

variable (α : L → R) (β : Weight R L M)

/-- The first weight in an `α`-chain through `β`. -/
noncomputable
def chainBot (α : L → R) (β : Weight R L M) : Weight R L M :=
  ⟨(- chainBotCoeff α β : ℤ) • α + β, genWeightSpace_neg_zsmul_add_ne_bot α β le_rfl⟩

end
end LieModule
end
