public section

namespace CFSG.RankThree.PartTwo.Sec3.Sims321

open scoped MatrixGroups

open Matrix CFSG.RankThree.FFModules CFSG.LocalAnalysis.ComponentInitial.LinearFlag

open CFSG.ComponentClassification CFSG CFSG.RankThree.PartTwo

theorem le_normalizer_omegaZOf {G : Type*} [Group G] (X : Subgroup G) :
    X ≤ Subgroup.normalizer (omegaZOf (CFSG.Open.pCoreOf 2 X) : Set G) :=
  (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X).trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)

end CFSG.RankThree.PartTwo.Sec3.Sims321
end
