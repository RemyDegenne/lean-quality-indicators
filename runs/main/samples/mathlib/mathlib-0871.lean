@[expose] public section

set_option linter.style.longFile 1600

open Function Fintype Nat Pointwise Subgroup Submonoid

open scoped Finset

variable {G H A α β : Type*}

section Group

variable [Group G] {x y : G} {i : ℤ}

@[to_additive]
theorem orderOf_dvd_iff_zpow_eq_one : (orderOf x : ℤ) ∣ i ↔ x ^ i = 1 := by
  rcases Int.eq_nat_or_neg i with ⟨i, rfl | rfl⟩
  · rw [Int.natCast_dvd_natCast, orderOf_dvd_iff_pow_eq_one, zpow_natCast]
  · rw [dvd_neg, Int.natCast_dvd_natCast, zpow_neg, inv_eq_one, zpow_natCast,
      orderOf_dvd_iff_pow_eq_one]

end Group
end
