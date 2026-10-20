@[expose] public section

open scoped BigOperators

open Finset

namespace BooleanIsoperimetry

theorem harper_macaulay_min {N a b : ℕ} (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N) :
    H (N + 1) (a + b) ≤ max (H N a) b + max (H N b) a := by
  suffices key : ∀ n, ∀ a b : ℕ, a ≤ 2 ^ n → b ≤ 2 ^ n →
      H (n + 1) (a + b) ≤ max (H n a) b + max (H n b) a by
    exact key N a b ha hb
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b ha hb
    have hS : a + b ≤ 2 ^ (n + 1) := by
      have h2 : (2 : ℕ) ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; ring
      omega
    obtain ⟨p, q, hp, hq, hpq, hcasc⟩ := exists_cascade_split n (a + b) hS
    rw [H_succ_cascade hcasc]
    exact macaulay_bc_min n ih ha hb hp hq hpq hcasc

end BooleanIsoperimetry
end
