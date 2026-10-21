namespace OAI

noncomputable section

namespace TreeEdit.BinaryLower

universe u

lemma le_finiteSourceLength {k : ℕ} (hk : 0 < k) : k ≤ finiteSourceLength k := by
  have hp : 1 ≤ k ^ (20 * k) := Nat.one_le_pow _ _ hk
  have hb : k ≤ 20 * k * k ^ (20 * k) := by
    have := Nat.mul_le_mul_left (20 * k) hp
    nlinarith
  exact hb.trans (Nat.le_pow hk)

end TreeEdit.BinaryLower
end
end OAI
