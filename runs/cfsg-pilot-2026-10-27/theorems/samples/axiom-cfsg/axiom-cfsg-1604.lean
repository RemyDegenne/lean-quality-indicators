public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LieType.BorelTits (orthGroup)

open CFSG.Blueprint (LieModel)

open CFSG.ComponentClassification.CatLeafProof (IsChar2LieShape)

open CFSG.ComponentClassification.CatLeafProof

open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section Certified

theorem conjClosure_eq_and_bar2_equiv_of_hyp18 {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L : Subgroup G} (h : Hyp18 D V₀ V p L)
    (hs : IsSimpleGroup ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L))) :
    conjClosure D.M L = L ∧
      Nonempty (Bar2 L ≃* ↥(barSub V₀ V h.hyp125.isElemAbelian L)) := by
  have hXL : conjClosure D.M L = L :=
    conjClosure_eq_self_of_isSimpleGroup_barSub h.hyp125 h.hL.1 hs
  have hL1 : barSub V₀ V h.hyp125.isElemAbelian L ≠ ⊥ := by
    have hne : barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L) ≠ ⊥ :=
      (Subgroup.nontrivial_iff_ne_bot _).1 hs.toNontrivial
    rw [hXL] at hne
    exact hne
  exact ⟨hXL, barSubBar2Equiv_of_isSimpleGroup h.hyp125 h.hL.1 hL1
    (isSimpleGroup_bar2_of_hyp18 h hXL)⟩

end Certified
end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
end
