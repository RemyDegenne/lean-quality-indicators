namespace OAI

namespace ThorpNine.Smoothing

namespace Thorp

open scoped BigOperators

open Filter

lemma card_tapes_succ (d t : ℕ) : Fintype.card (Fin t → Coins (d + 1)) = 2 ^ (t * 2 ^ d) := by
  rw [Fintype.card_fun, card_coins_succ, Fintype.card_fin, ← pow_mul, Nat.mul_comm]

end Thorp
end ThorpNine.Smoothing
end OAI
