public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieU6

open CFSG.Open CFSG.Fischer CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer

open CFSG.LocalAnalysis.GLTheoremA.LevelLieU

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open CFSG.ClassicalGroups.UnitaryFlag

open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

theorem isSimple_S6 : IsSimpleGroup S6 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F4 2 1 hF4card 6
    (by norm_num) (by norm_num)

end CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
end
