public section

namespace CFSG.GH74.GLS.Stage2.Local.Prop28

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GorensteinWalter

theorem isSimpleGroup_of_isL2 {X : Type} [Group X] {r : ℕ} (hr3 : 3 < r)
    (h : IVK.IsL2 X (fun s => s = r)) : IsSimpleGroup X := by
  obtain ⟨F, hF, hfin, hq, ⟨e⟩⟩ := h
  have h4 : 4 ≤ Nat.card F := by omega
  have : IsSimpleGroup (PSL2 F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  exact (e.trans (IVK.L2.equivPSL F)).isSimpleGroup

end CFSG.GH74.GLS.Stage2.Local.Prop28
end
