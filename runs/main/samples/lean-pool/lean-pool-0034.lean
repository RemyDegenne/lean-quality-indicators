@[expose] public section

open scoped BigOperators

namespace Core4027

section

variable (s t₀ t : ℕ)

variable (hs : s.Prime) (hs6 : ¬ s ∣ 6)

variable (ht₀ : 1 ≤ t₀ ∧ t₀ ≤ N * s ^ 3)

variable (hcong : t₀ % N = 23016 % N)

variable (hH : s ^ 3 ∣ Hpoly t₀) (hC : ¬ s ∣ Cpoly t₀)

variable (ht : t = t₀ + N * s ^ 3)

include hcong ht in
theorem L1 : N ∣ Gpoly t := by
  have h_gt_mod : Gpoly t ≡ Gpoly 23016 [MOD N] :=
    Gpoly_modEq (t_mod_N s t₀ t hcong ht)
  exact (Nat.modEq_zero_iff_dvd).mp (h_gt_mod.trans Gpoly_const_modN)

end
end Core4027
end
