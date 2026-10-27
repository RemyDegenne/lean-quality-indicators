public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)

variable {G : Type} [Group G] [Finite G]

theorem uc22p22c_pCoreOf_le_T (D : Data G) : pCoreOf 2 D.M ≤ D.T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := D.sylowM.exists_sylow_eq_subgroupOf
  have h := CFSG.fitting_pCore_le_sylow S
  rw [hS] at h
  exact Subgroup.map_le_iff_le_comap.2 h

end CFSG.LocalAnalysis.UniquenessCase.UC22
end
