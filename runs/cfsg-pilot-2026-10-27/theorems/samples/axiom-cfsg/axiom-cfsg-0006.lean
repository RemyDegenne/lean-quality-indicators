public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover

namespace TableBExc.E6Three

open TableBExc.Three

local instance tableBExcE6ThreeNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

local instance tableBExcE6ThreeFactThree : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem gE6_comm (i j : Fin 3) : gE6 i * gE6 j = gE6 j * gE6 i := by
  refine ext_single fun k => ?_
  rw [mul_smul, mul_smul, gE6, gE6, wordProd_smul, wordProd_smul, wordProd_smul, wordProd_smul]
  revert i j k
  decide +kernel

end TableBExc.E6Three
end CFSG.StandardType
end
