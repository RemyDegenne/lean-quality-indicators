public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional

open CFSG.LocalAnalysis.EvenBN.Common (CosetData)

open scoped commutatorElement Pointwise

theorem three_le_of_card_eq {K : Type*} {f : ℕ} (hK : Nat.card K = 2 ^ f) (h8 : 8 ≤ Nat.card K) :
    3 ≤ f := by
  by_contra hf
  have : 2 ^ f ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end CFSG.LocalAnalysis.EvenBN.G2
end
