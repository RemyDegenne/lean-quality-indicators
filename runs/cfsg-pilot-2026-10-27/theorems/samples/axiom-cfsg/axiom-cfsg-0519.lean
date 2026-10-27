public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

local instance e6PilotAlignToriNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

variable {K : Type} [Field K]

theorem iform_single_right_E6 (δ : Fin (Tag.rank .E6) → ℤ) (l : Fin (Tag.rank .E6)) :
    iform δ (Pi.single l 1) = ∑ j, δ j * Tag.cartan .E6 j l := by
  simp only [iform, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, symmetrizedCartan_E6]

end CFSG.SeitzReduction.E6Pilot
end
