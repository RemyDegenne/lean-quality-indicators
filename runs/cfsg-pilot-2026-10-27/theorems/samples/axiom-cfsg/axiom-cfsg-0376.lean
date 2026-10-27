public section

universe u

namespace CFSG.Timmesfeld.Bridge

open CFSG.QuasithinUnique.Setup.SL2Modules

open scoped MatrixGroups

namespace RootMany

theorem two_mul_le_two_pow {k : ℕ} (hk : 1 ≤ k) : 2 * k ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have h2 : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    rw [pow_succ]
    omega

end RootMany
end CFSG.Timmesfeld.Bridge
end
