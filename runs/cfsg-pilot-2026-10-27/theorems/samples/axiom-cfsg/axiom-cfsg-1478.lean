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

theorem coord_pow (f : Multiplicative V3 ≃* A) (v : V3) (k : ZMod 3) :
    f (Multiplicative.ofAdd v) ^ k.val = f (Multiplicative.ofAdd (k • v)) := by
  rw [← map_pow, ← ofAdd_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]

end URoots
end CFSG.RankThree.PartTwo.Sec21
end
