public section

variable {K : Type*} [Field K] {ι ι' : Type*} [Fintype ι] [Finite ι']

open MvPolynomial

variable {K : Type*} [Field K] {ι : Type*}

namespace Height

variable {K : Type*} [Field K] {ι ι' : Type*} [Fintype ι']

variable [AdmissibleAbsValues K] [Finite ι]

open AdmissibleAbsValues

theorem mulHeight_eval_ge {M N : ℕ} {q : ι × ι' → MvPolynomial ι K}
    (hq : ∀ a, (q a).IsHomogeneous M) (p : ι' → MvPolynomial ι K) {x : ι → K}
    (h : ∀ k, ∑ j, (q (k, j)).eval x * (p j).eval x = (x k) ^ (M + N)) :
    (Nat.card ι' ^ totalWeight K * max (mulHeightBound q) 1)⁻¹ * mulHeight x ^ N ≤
      mulHeight (fun j ↦ (p j).eval x) := by
  rcases isEmpty_or_nonempty ι'
  · simp [show q = 0 from Subsingleton.elim .., max_mulHeightBound_zero_one_eq_one K ι (ι × ι'),
      mulHeight_eval_ge_aux p h]
    grind [zero_pow_eq]
  -- case `ι'` nonempty
  let q' : ι × ι' → K := fun a ↦ (q a).eval x
  have H : mulHeight x ^ (M + N) ≤
      Nat.card ι' ^ totalWeight K * mulHeight q' * mulHeight fun j ↦ (p j).eval x := by
    rw [← mulHeight_pow x (M + N)]
    have : x ^ (M + N) = fun k ↦ ∑ j, (q (k, j)).eval x * (p j).eval x := funext fun k ↦ (h k).symm
    simpa [this] using mulHeight_linearMap_apply_le q' _
  rw [inv_mul_le_iff₀ ?hC, ← mul_le_mul_iff_left₀ (by positivity : 0 < mulHeight x ^ M)]
  case hC => exact mul_pos (mod_cast Nat.one_le_pow _ _ Nat.card_pos) <| by positivity
  rw [← pow_add, add_comm]
  grw [H, mulHeight_eval_le hq x]
  exact Eq.le (by ring)

end Height
end
