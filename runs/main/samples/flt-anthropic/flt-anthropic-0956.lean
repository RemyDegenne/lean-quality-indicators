namespace P2MW.S_ModularCurve_UVCrossingModel_finsum_rank_mul_length_eq_circleIndexDrop

set_option maxHeartbeats 800000

set_option autoImplicit false

universe u

set_option autoImplicit false

set_option autoImplicit false

open Finset BigOperators

set_option autoImplicit false

p2m_open

open scoped TensorProduct

p2m_open

p2m_reactivate

p2m_reactivate

p2m_open

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

universe v w

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_open

open scoped TensorProduct

open scoped TensorProduct

p2m_reactivate

section CharpolyCorollary

p2m_open

p2m_reactivate

namespace P1Depth

p2m_open

section NF

variable {W : Type u} [CommRing W]

theorem termOrder_U_mul_shift (v : W → ℕ∞) (E t : ℕ) (ht : t ≤ E) (π : W) (hπ : ∀ c, v (π * c) = (E : ℕ∞) + v c)
    (ab : PowerSeries W × PowerSeries W) (n : ℤ) :
    termOrder v E t
        (PowerSeries.mk fun i => if i = 0 then π * PowerSeries.coeff 1 ab.2 else PowerSeries.coeff (i - 1) ab.1,
          PowerSeries.mk fun j => if j = 0 then 0 else π * PowerSeries.coeff (j + 1) ab.2) n =
      termOrder v E t ab (n - 1) + (t : ℕ∞) := by
  rcases n with (_ | i) | j
  · have h : ((0 : ℕ) : ℤ) - 1 = Int.negSucc 0 := by decide
    rw [Int.ofNat_eq_natCast, termOrder_natCast, h, termOrder_negSucc]
    simp only [PowerSeries.coeff_mk, if_true, zero_mul, Nat.cast_zero, add_zero, zero_add, one_mul]
    rw [hπ, add_comm (E : ℕ∞), add_assoc, ← Nat.cast_add, Nat.sub_add_cancel ht]
  · have h : ((i + 1 : ℕ) : ℤ) - 1 = (i : ℕ) := by push_cast; ring
    rw [Int.ofNat_eq_natCast, termOrder_natCast, h, termOrder_natCast]
    simp only [PowerSeries.coeff_mk, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    rw [add_assoc, ← Nat.cast_add, Nat.succ_mul]
  · have h : Int.negSucc j - 1 = Int.negSucc (j + 1) := by rfl
    rw [h, termOrder_negSucc, termOrder_negSucc]
    simp only [PowerSeries.coeff_mk, Nat.add_one_ne_zero, if_false]
    have key : (E : ℕ∞) + (((j + 1) * (E - t) : ℕ) : ℕ∞) = (((j + 1 + 1) * (E - t) : ℕ) : ℕ∞) + (t : ℕ∞) := by
      rw [← Nat.cast_add, ← Nat.cast_add]
      congr 1
      obtain ⟨s, rfl⟩ : ∃ s, E = t + s := ⟨E - t, by omega⟩
      rw [Nat.add_sub_cancel_left]
      ring
    rw [hπ, add_comm (E : ℕ∞), add_assoc, key, ← add_assoc]

end NF
end P1Depth
end CharpolyCorollary
end P2MW.S_ModularCurve_UVCrossingModel_finsum_rank_mul_length_eq_circleIndexDrop
