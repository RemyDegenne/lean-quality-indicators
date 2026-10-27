public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.ClassicalGroups.Unitary CFSG.LocalAnalysis.RankThreeUC Matrix

open CFSG.LieType.Universal.Unitary (SUid)

variable {G : Type} [Group G] [Finite G]

section Transfer

variable {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} {L : Subgroup G}
  (F : UFrame V₀ V hV L)

theorem UFrame.mem_fixV_iff_fixSp {X : Subgroup (MulAut (Vtil V₀ V hV))}
    (hX : X ≤ lBar V₀ V hV L) (w : Vtil V₀ V hV) :
    w ∈ fixV X ↔ F.vec w ∈ fixSp (F.suSub X) := by
  constructor
  · intro hw a ha
    have hπ : (F.π a : MulAut (Vtil V₀ V hV)) ∈ X := (F.mem_suSub X a).1 ha
    have h := (mem_fixV (X := X) (v := w)).1 hw (F.π a) hπ
    rw [← F.vec_action a w, h]
  · intro hw x hx
    let a : ↥(SUid F.σ 4) := F.π.symm ⟨x, hX hx⟩
    have ha : a ∈ F.suSub X := by
      rw [F.mem_suSub]
      simpa [a] using hx
    have hv : a • F.vec w = F.vec w := (mem_fixSp (E := F.suSub X) (x := F.vec w)).1 hw a ha
    have hfix : (F.π a : MulAut (Vtil V₀ V hV)) w = w := by
      apply F.vec_injective
      rw [F.vec_action]
      exact hv
    simpa [a] using hfix

end Transfer
end CFSG.LocalAnalysis.UniquenessCase.PartTwo
end
