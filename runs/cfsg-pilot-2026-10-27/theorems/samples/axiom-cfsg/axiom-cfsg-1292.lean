public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp

open CFSG.ABGLocalTools (IsSylowOf)

open CFSG.ComponentClassification.AschbacherTightEmbedding (rightConjugate)

local notation "actΓ" => CFSG.RankThree.PartOne.U5K.Hyp.act

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem Hyp.card_V₁ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    Nat.card d.V₁ = (2 ^ f) ^ 4 := by
  rw [V₁, card_map_of_injective (MulAut.conj d.s).injective, hd.card_F_I₄ hGMS]

end Data
end CFSG.LocalAnalysis.EvenBN.U5
end
