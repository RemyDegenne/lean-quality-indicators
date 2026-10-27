public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallBad.AltTwoP

open Equiv Equiv.Perm CFSG.AGLEmbedding.KFactProofs.RankOneCore

variable {p : ℕ}

theorem swapS_conj_bmul (c₀ c₁ : (ZMod p)ˣ) :
    swapS * bmul c₀ c₁ * swapS⁻¹ = bmul c₁ c₀ := by
  rw [swapS_inv]
  ext ⟨i, z⟩ <;> fin_cases i <;> simp [bmul]

end CFSG.AGLEmbedding.KFactProofs.SmallBad.AltTwoP
end
