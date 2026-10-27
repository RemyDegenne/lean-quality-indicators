public noncomputable section

namespace CFSG.RankThree.PartOne.KC1

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE8F

open CFSG.RankThree.Lattice

open CFSG.RankThree.E6 (chainRoot)

open scoped MatrixGroups

set_option linter.unusedSectionVars false

theorem orth3 : ∀ i j k l : Fin 5, i ≠ j → k ≠ l →
    toVec Tag.E8.rank (e8a4rootL (e8wl omega3) i j) ⬝ᵥ
      (Tag.E8.symmetrizedCartan *ᵥ toVec Tag.E8.rank
        (lmulVec Tag.E8.rank e8P4VList (e8a4rootL (e8wl omega3) k l))) = 0 := by
  decide +kernel

end CFSG.RankThree.PartOne.KC1
end
