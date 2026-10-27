public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem barO2Z17_equiv_barInf {M L : Subgroup G} (hL : L ∈ calC M) :
    Nonempty (BarO2Z17 L ≃* BarInf L) :=
  ⟨QuotientGroup.quotientMulEquivOfEq (o2zIn17_eq_solvableRadical hL)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
end
