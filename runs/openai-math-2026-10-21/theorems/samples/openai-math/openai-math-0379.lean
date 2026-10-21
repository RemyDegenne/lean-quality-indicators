namespace OAI

namespace ThorpNine.Casimir

namespace Thorp

lemma palindromePerm_reverse (d : ℕ) (ω : BenesCoins d) :
    palindromePerm d (ω.2,ω.1) = (palindromePerm d ω)⁻¹ := by
  simp only [palindromePerm,mul_inv_rev]
  rfl

end Thorp
end ThorpNine.Casimir
end OAI
