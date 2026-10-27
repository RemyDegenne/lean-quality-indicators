public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

open CFSG.RankThree.PartTwo.KFacts (centerDescend)

theorem k432ListP_of_goodRow (PL : ∀ (L : Type) [Group L] [Finite L], Prop)
    (hrow : ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L → PL L →
      GoodRow (L ⧸ Subgroup.center L)) : K432ListP PL := by
  intro L _ _ hq hS hZ3 Z hZ hwc hnc
  haveI : Group.IsPerfect L := hq.1
  haveI : IsSimpleGroup (L ⧸ Subgroup.center L) := hq.2.1
  obtain ⟨z, hzo, rfl⟩ := Item432Proof.exists_zpowers_eq hZ
  have hzc : z ∉ Subgroup.center L := fun h => hnc (Subgroup.zpowers_le.mpr h)
  have hz3 : z ^ 3 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one z
  have hbar : WeaklyClosed (Subgroup.zpowers (QuotientGroup.mk z : L ⧸ Subgroup.center L)) :=
    weaklyClosed_mk_zpowers hzo hzc hwc
  have hzbar3 : (QuotientGroup.mk z : L ⧸ Subgroup.center L) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hz3, QuotientGroup.mk_one]
  have hzbar1 : (QuotientGroup.mk z : L ⧸ Subgroup.center L) ≠ 1 := fun h1 =>
    hzc ((QuotientGroup.eq_one_iff z).mp h1)
  obtain ⟨hlist, -⟩ := hrow L hq hS
  rcases hlist _ (orderOf_eq_prime hzbar3 hzbar1) hbar with h1 | ⟨hG2, -, hno⟩ | ⟨hJ2, -, hno⟩
  · have hbot : Subgroup.center L = ⊥ :=
      center_eq_bot_of_pRank_quot_le_one hq.1 hZ3 h1.le
    left
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num)
      (mulEquivQuotCenterOfEqBot hbot)]
    exact h1
  · have hbot : Subgroup.center L = ⊥ := hno L hq hZ3 ⟨MulEquiv.refl _⟩
    right; left
    obtain ⟨e⟩ : Nonempty (L ≃* (L ⧸ Subgroup.center L)) := ⟨mulEquivQuotCenterOfEqBot hbot⟩
    rcases hG2 with ⟨p, f, hm⟩ | he'
    · exact Or.inl ⟨p, f, CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e hm⟩
    · obtain ⟨e'⟩ := he'
      exact Or.inr ⟨e.trans e'⟩
  · have hbot : Subgroup.center L = ⊥ := hno L hq hZ3 ⟨MulEquiv.refl _⟩
    right; right
    obtain ⟨e'⟩ := hJ2
    exact ⟨(mulEquivQuotCenterOfEqBot hbot).trans e'⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
end
