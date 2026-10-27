public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open CFSG.Quasithin (perfectCore)

local instance f4PilotAlignLeviToriNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section Subfield

variable {k K : Type} [Field k] [Field K]

theorem perfectCore_inf_centralizer_map_leviTorus [Finite k] (f : k →+* K)
    (hq : 4 ≤ Nat.card k) {J : Finset (Fin (Tag.rank .F4))} (hJ : J.card ≤ 2) :
    perfectCore (adjointGroup .F4 K ⊓
        centralizer (((leviTorus k J).map (baseChangeGL f) : Subgroup (ModGL .F4 K)) :
          Set (ModGL .F4 K))) =
      rootSpan .F4 K (amalgamRoots J) := by
  rw [map_baseChangeGL_leviTorus]
  exact perfectCore_inf_centralizer_leviTorusOf _ (three_le_natCard_range_unitsMap f hq) hJ

end Subfield
end CFSG.SeitzReduction.F4Pilot
end
