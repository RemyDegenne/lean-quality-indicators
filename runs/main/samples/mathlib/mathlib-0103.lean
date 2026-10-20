public section

open scoped Nat

namespace ZMod

section Products

theorem isCyclic_units_four_mul_iff (n : ℕ) :
    IsCyclic (ZMod (4 * n))ˣ ↔ n = 0 ∨ n = 1 := by
  obtain rfl | hn0 := eq_or_ne n 0
  · simp [isCyclic_units_zero]
  obtain rfl | hn1 := eq_or_ne n 1
  · simp [isCyclic_units_four]
  refine iff_of_false ?_ (by simp [hn0, hn1])
  obtain ⟨n, rfl⟩ | h2n := em (2 ∣ n)
  · rw [← mul_assoc]
    have : NeZero n := ⟨by simpa using hn0⟩
    refine mt (fun _ ↦ ?_) not_isCyclic_units_eight
    exact isCyclic_of_surjective _ (ZMod.unitsMap_surjective (m := 4 * 2 * n) (dvd_mul_right 8 _))
  have : Nat.Coprime 4 n := (Nat.prime_two.coprime_iff_not_dvd.mpr h2n).pow_left 2
  rw [((Units.mapEquiv (chineseRemainder this).toMulEquiv).trans .prodUnits).isCyclic,
    Group.isCyclic_prod_iff]
  rintro ⟨-, -, h⟩
  have : NeZero n := ⟨hn0⟩
  have : Odd (φ n) := by simpa [show φ 4 = 2 from rfl] using h
  rw [Nat.odd_totient_iff] at this
  lia

end Products
end ZMod
end
