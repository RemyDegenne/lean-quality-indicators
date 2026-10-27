public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.BalanceFromYS

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn SporadicOrdersTable LocalTwoBalanceDefCharThree
  LocalTwoBalanceDefCharFive)

open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut)

open CFSG.HardMathSupport.Timmesfeld.Coordinator (IsLocallyBalancedAbs SporadicOuterLeTwo
  LocalThreeBalanceCrossChar)

open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges)

open CFSG.HardMathSupport.Timmesfeld.LocalTwo (LocalTwoBalanceSporadicGtFive IsLpEpsIndex
  LocalTwoBalanceCrossCharGtFive LocalTwoBalanceDefCharGtFive)

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

open Equiv Equiv.Perm

theorem input19_16Main_of_ys (h02 : LocalThreeBalanceCrossChar)
    (h03 : CFSG.Yardstones.M67c2c3e09a6b.LocalTwoBalanceThreeFive) (h04 : LocalTwoBalanceCrossCharGtFive)
    (h04s : LocalTwoBalanceSporadicGtFive) (hd3 : LocalTwoBalanceDefCharThree)
    (hd5 : LocalTwoBalanceDefCharFive) (hd7 : LocalTwoBalanceDefCharGtFive) (hout : SporadicOuterLeTwo)
    (hbr : SporadicBridges) (hord : SporadicOrdersTable)
    (hFi : CFSG.RankThree.PartOne.Mult.SporadicKernelTrivial .Fi22 5) (hLp : Input19_16Lp) :
    Lemma129.Input19_16Main := by
  intro p k hp hp2 hk K _ _ hKG hq hO B hB hBc
  obtain ⟨hnab, i, ⟨f⟩⟩ := CFSG.HardMathSupport.Solomon.Coordinator.I1420.catalog_of_quasisimple hq hKG
  rcases i with ⟨p', hp'⟩ | ⟨n, hn⟩ | idx | s
  · exfalso
    obtain ⟨x, y, hxy⟩ := hnab
    apply hxy
    apply f.injective
    rw [map_mul, map_mul]
    have : ∀ x y : Multiplicative (ZMod p'), x * y = y * x := fun x y => mul_comm x y
    exact this _ _
  · rcases alt_case hp hp2 hk hq hO hn f B hB hBc with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases lie_case h02 h03 h04 hd3 hd5 hd7 hLp hp hp2 hk hq hO idx ⟨f⟩ B hB hBc with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
  · rcases spor_case h03 h04s hout hbr hord hFi hp hp2 hk hq hO ⟨f⟩ B hB hBc with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.BalanceFromYS
end
