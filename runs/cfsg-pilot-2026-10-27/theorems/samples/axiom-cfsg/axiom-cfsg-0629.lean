public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

open CFSG.Quasithin (perfectCore)

local instance e6PilotCoverFamilyTwistNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

section Piece

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  [Finite G] {L : Subgroup G} {e : L ≃* adjointGroup .E6 (fixSubfield σ)}

variable {N : E6Neighbour} {c : FieldNeighbourCover σ e N} {J : Finset (Fin (Tag.rank .E6))}
  {hJ : J ⊆ N.nodes}
  {s : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J →* neighbourCore e N}

theorem levi_eq_iSup_singleton (K : Type) [Field K] (J : Finset (Fin (Tag.rank .E6))) :
    CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J =
      ⨆ j ∈ J, CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {j} := by
  simp only [CFSG.LieType.CurtisTits.levi_singleton]
  rfl

end Piece
end CFSG.SeitzReduction.E6Pilot
end
