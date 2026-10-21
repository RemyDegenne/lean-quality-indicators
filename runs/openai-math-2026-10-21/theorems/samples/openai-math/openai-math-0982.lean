namespace OAI

open Filter

open scoped Topology

namespace Invariant233.MixedRadix

@[simp] theorem prefixRank_zero {r : ℕ → ℕ} (d : Digits r) : prefixRank d 0 = 0 := rfl

end Invariant233.MixedRadix
end OAI
