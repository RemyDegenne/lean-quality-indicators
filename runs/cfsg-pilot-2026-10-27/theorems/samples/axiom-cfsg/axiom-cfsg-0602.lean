public section

namespace CFSG.Goldschmidt.Sec8

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G}

omit [Finite G] in
theorem mem_zpowers_pow_of_sq_eq_one {g t : G} {n : ℕ} (hg : orderOf g = 2 ^ (n + 1))
    (ht : t ∈ Subgroup.zpowers g) (ht2 : t ^ 2 = 1) :
    t ∈ Subgroup.zpowers (g ^ (2 ^ n)) := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
  have h1 : g ^ (k * 2) = 1 := by
    rw [zpow_mul, ← ht2]
    norm_cast
  rw [← orderOf_dvd_iff_zpow_eq_one, hg] at h1
  have h2 : ((2 : ℤ) ^ n) ∣ k := by
    have h3 : ((2 : ℤ) ^ n * 2) ∣ k * 2 := by
      have := h1
      push_cast [pow_succ] at this
      exact this
    exact (mul_dvd_mul_iff_right two_ne_zero).mp h3
  obtain ⟨l, rfl⟩ := h2
  refine Subgroup.mem_zpowers_iff.mpr ⟨l, ?_⟩
  rw [zpow_mul]
  norm_cast

end CFSG.Goldschmidt.Sec8
end
