@[expose] public section

open Module Polynomial

namespace IntermediateField

section AdjoinIntegralElement

universe u

variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E] {α : E}

variable {K : Type u} [Field K] [Algebra F K]

section PowerBasis

variable {L : Type*} [Field L] [Algebra K L]

theorem adjoin_eq_top_of_adjoin_eq_top [Algebra E K] [IsScalarTower F E K]
    {S : Set K} (hprim : adjoin F S = ⊤) : adjoin E S = ⊤ :=
  restrictScalars_injective F <| by
    rw [restrictScalars_top, ← top_le_iff, ← hprim, adjoin_le_iff,
      coe_restrictScalars, ← adjoin_le_iff]

end PowerBasis
end AdjoinIntegralElement
end IntermediateField
end
