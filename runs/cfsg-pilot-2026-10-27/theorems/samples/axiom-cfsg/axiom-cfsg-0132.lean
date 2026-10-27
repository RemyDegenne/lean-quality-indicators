public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup

open CFSG.Blueprint (LieModel)

open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor)

open CFSG.ClassicalGroups.UnitaryFlag (unitarySU unitaryPSU unitaryProj unitaryProj_surjective
  unitaryPSUEquiv)

open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

theorem isCyclic_of_inf_inner_eq_bot_of_psl_two_two {K : Type} [Group K] [Finite K] {f : ℕ}
    (hK : LieModel K .PSL 2 2 f) (W : Subgroup (MulAut K)) (hW : IsPGroup 2 W)
    (hWi : W ⊓ (MulAut.conj : K →* MulAut K).range = ⊥) : IsCyclic W := by
  have := UC22.P22y.isCyclic_outer_of_isL2Ev (UC22.P22fin.isL2Ev_of_isL2 hK).1
  exact r1f2_isCyclic_of_outer (fun _ _ => inferInstance) hW hWi

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
end
