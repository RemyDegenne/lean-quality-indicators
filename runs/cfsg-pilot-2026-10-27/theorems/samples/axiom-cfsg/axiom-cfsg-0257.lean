public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieU4E

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48 (SU4 μ3 torusSU4 Dstd)

open CFSG.LocalAnalysis.GLTheoremA.CatB.U48

open scoped commutatorElement

open Matrix

open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIV (torusSnoc torusSnoc_castSucc torusSnoc_last)

open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K hK card_K card_units_K)

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

open scoped commutatorElement

open CFSG.LocalAnalysis.GLTheoremA.CatB.U48

open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48

open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K hK card_K card_units_K)

open Matrix

open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIV (torusSnoc torusSnoc_castSucc torusSnoc_last)

theorem mat_yStd_zetaU (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    mat (yStd (zetaU ζ hζ)) = diagonal ![ζ, ζ, ζ, 1] := by
  rw [mat_yStd]
  congr 1
  funext k
  fin_cases k <;> simp [zetaU_val]

end CFSG.LocalAnalysis.GLTheoremA.LevelLieU4E
end
