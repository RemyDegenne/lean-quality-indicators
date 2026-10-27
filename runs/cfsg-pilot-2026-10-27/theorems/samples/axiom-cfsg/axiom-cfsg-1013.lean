public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

variable {G : Type*} [Group G]

section Helpers

theorem dihedral_central_involution {r x : G} {k : ℕ} (hr : r * r = 1) (hx : x * x = 1)
    (hk : orderOf (r * x) = 2 * k) (hk0 : 0 < k) :
    (r * x) ^ k * (r * x) ^ k = 1 ∧ (r * x) ^ k ≠ 1 ∧
      (r * x) ^ k * r = r * (r * x) ^ k ∧ (r * x) ^ k * x = x * (r * x) ^ k ∧
      (IsConj r ((r * x) ^ k * r) ∨ IsConj r ((r * x) ^ k * x)) := by
  generalize hs : r * x = s at hk ⊢
  have hr' : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hs2k : s ^ (2 * k) = 1 := hk ▸ pow_orderOf_eq_one s
  have hz1 : s ^ k * s ^ k = 1 := by rw [← pow_add, ← two_mul, hs2k]
  have hzinv : (s ^ k)⁻¹ = s ^ k := inv_eq_of_mul_eq_one_right hz1
  have hne : s ^ k ≠ 1 := pow_ne_one_of_lt_orderOf hk0.ne' (by omega)
  have hrs : r * s * r = s⁻¹ := by
    rw [← hs, mul_inv_rev, hx', hr']
    calc r * (r * x) * r = (r * r) * x * r := by group
      _ = x * r := by rw [hr, one_mul]
  have hxs : x * s * x = s⁻¹ := by
    rw [← hs, mul_inv_rev, hx', hr']
    calc x * (r * x) * x = x * r * (x * x) := by group
      _ = x * r := by rw [hx, mul_one]
  have hpowr : ∀ n : ℕ, r * s ^ n * r = (s ^ n)⁻¹ := by
    intro n
    have := conj_pow (a := r) (b := s) (i := n)
    rw [hr'] at this
    rw [← this, hrs, inv_pow]
  have hpowx : ∀ n : ℕ, x * s ^ n * x = (s ^ n)⁻¹ := by
    intro n
    have := conj_pow (a := x) (b := s) (i := n)
    rw [hx'] at this
    rw [← this, hxs, inv_pow]
  have hzr : s ^ k * r = r * s ^ k := by
    have h := hpowr k
    rw [hzinv] at h
    calc s ^ k * r = r * s ^ k * r * r := by rw [h]
      _ = r * s ^ k := by rw [mul_assoc (r * s ^ k) r r, hr, mul_one]
  have hzx : s ^ k * x = x * s ^ k := by
    have h := hpowx k
    rw [hzinv] at h
    calc s ^ k * x = x * s ^ k * x * x := by rw [h]
      _ = x * s ^ k := by rw [mul_assoc (x * s ^ k) x x, hx, mul_one]
  refine ⟨hz1, hne, hzr, hzx, ?_⟩
  obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' k
  all_goals
    have hconj : s ^ j * r * (s ^ j)⁻¹ = s ^ (2 * j) * r := by
      rw [← hpowr j]
      calc s ^ j * r * (r * s ^ j * r) = s ^ j * (r * r) * s ^ j * r := by group
        _ = s ^ (2 * j) * r := by rw [hr, mul_one, ← pow_add, two_mul]
  · left
    exact isConj_iff.mpr ⟨s ^ j, by rw [hconj, hj]⟩
  · right
    refine isConj_iff.mpr ⟨s ^ j, ?_⟩
    rw [hconj, hj]
    have hsx : s * x = r := by rw [← hs, mul_assoc, hx, mul_one]
    calc s ^ (2 * j) * r = s ^ (2 * j) * (s * x) := by rw [hsx]
      _ = s ^ (2 * j + 1) * x := by rw [pow_succ, mul_assoc]

end Helpers
end CFSG.Monster.GMS
end
