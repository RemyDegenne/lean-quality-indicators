public section

namespace CFSG.AGLEmbedding

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Fischer.Classification
  CFSG.LieType.Steinberg.CentralExt.SUThreeFieldTwo

variable {F : Type} [Field F] [Finite F] [CharP F 2] {ζ : F}

section Group

variable (hσ : unitaryInvolution F 2 1 ζ = ζ ^ 2) (hs : 1 + ζ + ζ ^ 2 = 0)

theorem card_SUid_three_two (hF : Nat.card F = (2 ^ 1) ^ 2) :
    Nat.card (SUid (unitaryInvolution F 2 1) 3) = 216 := by
  obtain ⟨P, hP⟩ := exists_wittMatrix hF 3
  rw [← Nat.card_congr (conjEquiv P hP).toEquiv, CFSG.LieType.Steinberg.card_SU_three hF]
  norm_num

end Group
end CFSG.AGLEmbedding
end
