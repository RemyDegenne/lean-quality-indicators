namespace P2MW.S_ModularCurve_UVCrossingModel_finsum_rank_mul_length_eq_sInf_sub_sSup

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

namespace SlopeLawSol

p2m_open

open AnnulusNF AnnulusStepA

variable {W : Type u} [CommRing W]

theorem termOrder_succ_add (v : W → ℕ∞) (E t : ℕ) (hte : t + 1 ≤ E) (ab : PowerSeries W × PowerSeries W) (n : ℤ) :
    termOrder v E (t + 1) ab n + ((-n).toNat : ℕ∞) = termOrder v E t ab n + (n.toNat : ℕ∞) := by
  cases n with
  | ofNat i =>
    simp only [Int.ofNat_eq_natCast, termOrder_natCast, Int.toNat_natCast]
    have : (-(i : ℤ)).toNat = 0 := by simp
    rw [this, Nat.cast_zero, add_zero, add_assoc, ← Nat.cast_add, Nat.mul_succ]
  | negSucc j =>
    have hn : (-(Int.negSucc j)).toNat = j + 1 := by simp
    rw [termOrder_negSucc, termOrder_negSucc, hn, Int.toNat_negSucc, Nat.cast_zero, add_zero,
      add_assoc, ← Nat.cast_add]
    have h1 : E - t = (E - (t + 1)) + 1 := by omega
    have h2 : (j + 1) * (E - (t + 1)) + (j + 1) = (j + 1) * (E - t) := by rw [h1]; ring
    rw [h2]

end SlopeLawSol
end P2MW.S_ModularCurve_UVCrossingModel_finsum_rank_mul_length_eq_sInf_sub_sSup
