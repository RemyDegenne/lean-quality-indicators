public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

namespace Sec14

variable {c : Ctx12 Z M} {n : ℕ} {Q : Sylow 2 ↥c.L} {U : Subgroup X}

section Zsig

variable {r : ℕ}

theorem zsig_gt (hn : 1 ≤ n) (hr : r.Prime) (hdvd : r ∣ 2 ^ (6 * n) - 1)
    (hprim : ∀ k : ℕ, 0 < k → k < 6 * n → ¬ r ∣ 2 ^ k - 1) : 6 * n < r := by
  by_contra hle
  have hr2 := zsig_ne_two hn hdvd
  have hcop : Nat.Coprime 2 r := (Nat.coprime_primes Nat.prime_two hr).mpr (Ne.symm hr2)
  have hferm : 2 ^ (r - 1) ≡ 1 [MOD r] := by
    have := Nat.ModEq.pow_totient hcop
    rwa [Nat.totient_prime hr] at this
  have h1 : r ∣ 2 ^ (r - 1) - 1 := (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hferm.symm
  exact hprim (r - 1) (by have := hr.two_le; omega) (by omega) h1

end Zsig
end Sec14
end CFSG.GH74.Uniqueness
end
