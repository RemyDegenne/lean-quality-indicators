public section

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

local instance e8PilotAlignToriNeZeroRank : NeZero Tag.E8.rank := ⟨by decide⟩

variable {K : Type} [Field K]

theorem corootLine_le_leviTorus {J : Finset (Fin (Tag.rank .E8))} {δ : Fin (Tag.rank .E8) → ℤ}
    (h : ∀ j ∈ J, iform δ (Pi.single j 1) = 0) : corootLine K δ ≤ leviTorus K J := by
  rintro _ ⟨c, rfl⟩
  exact rootDiagUnit_corootTuple_mem_leviTorus h c

end CFSG.SeitzReduction.E8Pilot
end
