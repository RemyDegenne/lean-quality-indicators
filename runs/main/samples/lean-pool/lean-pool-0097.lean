public section

namespace PDT

namespace SalemArith

noncomputable section

open Polynomial Complex

lemma reflect_P_eq_Q (alpha : ℝ) (inside : Multiset ℂ) :
    (SalemCircle.P alpha inside).reflect (inside.card + 1)
      = SalemCircle.Q alpha inside := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hsub : ({(0 : ℂ)}ᶜ : Set ℂ) ⊆
      {x : ℂ |
        Polynomial.eval x ((SalemCircle.P alpha inside).reflect (inside.card + 1))
          = Polynomial.eval x (SalemCircle.Q alpha inside)} := by
    intro z hz
    have hz0 : z ≠ 0 := by simpa using hz
    let : Invertible z⁻¹ := invertibleOfNonzero (inv_ne_zero hz0)
    have key := Polynomial.eval₂_reflect_mul_pow (RingHom.id ℂ) z⁻¹
      (inside.card + 1) (SalemCircle.P alpha inside)
      (le_of_eq (SalemCircle.P_natDegree alpha inside))
    rw [Polynomial.eval₂_id, Polynomial.eval₂_id, invOf_eq_inv, inv_inv] at key
    have hzp : (z⁻¹) ^ (inside.card + 1) * z ^ (inside.card + 1) = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hz0, one_pow]
    change Polynomial.eval z ((SalemCircle.P alpha inside).reflect (inside.card + 1))
        = Polynomial.eval z (SalemCircle.Q alpha inside)
    calc Polynomial.eval z ((SalemCircle.P alpha inside).reflect (inside.card + 1))
        = Polynomial.eval z ((SalemCircle.P alpha inside).reflect (inside.card + 1))
          * ((z⁻¹) ^ (inside.card + 1) * z ^ (inside.card + 1)) := by
          rw [hzp, mul_one]
      _ = (Polynomial.eval z ((SalemCircle.P alpha inside).reflect (inside.card + 1))
          * (z⁻¹) ^ (inside.card + 1)) * z ^ (inside.card + 1) := by ring
      _ = Polynomial.eval z⁻¹ (SalemCircle.P alpha inside)
          * z ^ (inside.card + 1) := by rw [key]
      _ = z ^ (inside.card + 1) * (SalemCircle.P alpha inside).eval z⁻¹ := by ring
      _ = (SalemCircle.Q alpha inside).eval z := SalemCircle.mirror_P alpha inside hz0
  exact Set.Infinite.mono hsub ((Set.finite_singleton 0).infinite_compl)

end
end SalemArith
end PDT
end
