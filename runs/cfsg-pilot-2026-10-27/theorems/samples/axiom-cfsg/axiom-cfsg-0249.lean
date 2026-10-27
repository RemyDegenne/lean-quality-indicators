public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

open CFSG.RankThree.PartTwo.KFacts.KP14

open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

open CFSG.Assembly (IsElemAbelian)

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

open Matrix

namespace URoots

variable {G : Type} [Group G] {A : Subgroup G}

theorem coord_mul (f : Multiplicative V3 ≃* A) (v w : V3) :
    f (Multiplicative.ofAdd v) * f (Multiplicative.ofAdd w) =
      f (Multiplicative.ofAdd (v + w)) := by
  rw [← map_mul, ← ofAdd_add]

end URoots
end CFSG.RankThree.PartTwo.Sec21
end
