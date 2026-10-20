namespace P2MW.S_PadicAlgCl_norm_sum_pow_apply_le_of_mem_cyclotomicTower

set_option autoImplicit false

noncomputable section

namespace CTR

open Polynomial

variable (p : ℕ) [Fact p.Prime]

local notation "Ω" => PadicAlgCl p

local notation "Γ" => (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)

local notation "L" => PadicAlgCl.cyclotomicTower p

scoped instance finiteDimensional_L (n : ℕ) : FiniteDimensional ℚ_[p] (L n) :=
  Module.finite_of_finrank_pos (by rw [finrank_eq_e]; exact e_pos p n)

theorem T_pi_pow {k : ℕ} {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ (k + 2))) (σ : Γ) {a u : ℕ}
    (ha : a = 1 + p ^ (k + 1) * u) (hu : ¬ p ∣ u) (hσ : σ ζ = ζ ^ a) {i : ℕ} (hi : i < p) :
    T p σ ((ζ - 1) ^ i) = (-1) ^ i * p := by
  have hp : p.Prime := Fact.out
  have hexp : (ζ - 1) ^ i = ∑ m ∈ Finset.range (i + 1), ζ ^ m * ((-1) ^ (i - m) * (i.choose m : ℤ) : ℤ) := by
    rw [sub_eq_add_neg, add_pow]
    refine Finset.sum_congr rfl fun m _ => ?_
    push_cast; ring
  rw [hexp, T_sum]
  rw [Finset.sum_range_succ']
  have hzero : ∀ m ∈ Finset.range i,
      T p σ (ζ ^ (m + 1) * ((-1) ^ (i - (m + 1)) * (i.choose (m + 1) : ℤ) : ℤ)) = 0 := by
    intro m hm
    rw [Finset.mem_range] at hm
    rw [T_mul_intCast, T_zeta_pow_eq_zero p hζ σ ha hσ, zero_mul]
    intro hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
    · exact absurd (Nat.le_of_dvd (Nat.succ_pos m) h) (by omega)
    · exact hu h
  rw [Finset.sum_eq_zero hzero, zero_add, T_mul_intCast, pow_zero, T_one]
  push_cast
  simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
  ring

end CTR
end
end P2MW.S_PadicAlgCl_norm_sum_pow_apply_le_of_mem_cyclotomicTower
