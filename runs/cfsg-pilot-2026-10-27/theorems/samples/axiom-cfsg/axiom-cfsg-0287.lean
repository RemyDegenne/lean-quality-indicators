public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley RootSpace

open CFSG.Quasithin (perfectCore perfectCore_mono le_perfectCore_of_perfect)

local instance e6PilotAlignLeviNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

variable {K : Type} [Field K]

theorem exists_inner_ofLattice_eq_iform_E6 :
    ∃ c : ℝ, 0 < c ∧ ∀ u v : Fin (Tag.rank .E6) → ℤ,
      inner ℝ (ofLattice u) (ofLattice v) = c * (iform u v : ℝ) := by
  obtain ⟨c, hc, h⟩ := exists_inner_eq_smul .E6
  refine ⟨c, hc, fun u v => ?_⟩
  rw [h]
  congr 1
  simp only [ofLattice_apply, iform, Int.cast_sum, Int.cast_mul]

end CFSG.SeitzReduction.E6Pilot
end
