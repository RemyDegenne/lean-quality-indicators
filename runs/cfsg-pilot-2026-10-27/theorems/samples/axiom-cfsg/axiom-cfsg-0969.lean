public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld.Connectivity

open CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.WeakClosure81.SevenK

open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull
  CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther

open QuadraticMap Module CFSG.GroupTheory.WeirSylow CFSG.Open

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
theorem SpChart.le_ncard {hC : HypothesisC D} {hα : hC.alpha = {hC.d}} {k : ℕ} {F : Type}
    [Field F] [Finite F] [Finite G] (c : SpChart hC hα k F) :
    Nat.card F ^ (2 * k) - 1 ≤ (commSet D hC.d).ncard := by
  classical
  have hsub : {v : Fin k ⊕ Fin k → F | v ≠ 0} ⊆ c.vec '' commSet D hC.d := fun v hv => by
    obtain ⟨z, hz, rfl⟩ := c.exists_vec v hv
    exact ⟨z, hz, rfl⟩
  have h0 : {v : Fin k ⊕ Fin k → F | v ≠ 0} = Set.univ \ {0} := by
    ext v
    simp
  calc Nat.card F ^ (2 * k) - 1 = {v : Fin k ⊕ Fin k → F | v ≠ 0}.ncard := by
        rw [h0, Set.ncard_diff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ, natCard_vec]
    _ ≤ (c.vec '' commSet D hC.d).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (commSet D hC.d).ncard := Set.ncard_image_le (Set.toFinite _)

end CFSG.OddTranspositions.PartThree
end
