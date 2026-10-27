public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Fstar)

open CFSG.LocalAnalysis.UniquenessCase.PartTwo (InEGroup)

theorem sup_subgroupOf_eq_top {L₀ : Type} [Group L₀] {A S : Subgroup (MulAut L₀)}
    (hS : S ≤ A) (h : innAutOf L₀ ⊔ S = A) :
    (innAutOf L₀).subgroupOf A ⊔ S.subgroupOf A = ⊤ := by
  have hI : innAutOf L₀ ≤ A := h ▸ le_sup_left
  rw [← Subgroup.subgroupOf_sup hI hS, h]
  exact Subgroup.subgroupOf_self A

end CFSG.LocalAnalysis.WeakClosure81
end
