public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools

open CFSG.RankThree.PartOne (torusWeyl torusIrreducible)

open CFSG.RankThree.PartOne.LinAlg (bsub torusWeylGL wActionGL)

open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem fin3_ne (i : Fin 3) : i + 1 ≠ i ∧ i + 2 ≠ i ∧ i + 1 ≠ i + 2 := by
  revert i
  decide

end CFSG.LocalAnalysis.UniquenessCase.UC6
end
