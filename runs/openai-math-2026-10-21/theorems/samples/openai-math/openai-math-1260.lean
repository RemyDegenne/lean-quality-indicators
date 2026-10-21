namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory

open scoped ENNReal Topology ContDiff

namespace RVM

lemma scaled_two_level_crossing_sum {N D α γ : ℝ} (hN : 0<N) (hD : 0<D)
    (hα : 0<α) (hα1 : α<1) (hγ : 0<γ) (x : ℕ→ℝ) (hx : ∀j,0<x j) :
    (∑'nt : ℕ,∑'nr : ℕ,if x nt≤cappedRepresentative nr then
      ENNReal.ofReal (min ((N*(cappedRepresentative nt)^γ)*(cappedRepresentative nr/x nt)^α)
        ((D^2/(N*(cappedRepresentative nt)^γ))*(cappedRepresentative nr/x nt)^(-1:ℝ)))
      else 0)≤
      ENNReal.ofReal ((2+dyadicBalanceConstant α 1)*D*
        dyadicBalanceConstant (γ*((1-α)/(1+α))) γ) := by
  let q : ℝ := (1-α)/(1+α)
  let K : ℝ := (2+dyadicBalanceConstant α 1)*D
  have hq : 0<q := div_pos (sub_pos.mpr hα1) (by linarith)
  have hK : 0≤K := by dsimp [K]; positivity [dyadicBalanceConstant_pos hα (by norm_num : (0:ℝ)<1)]
  let g : ℤ→ℝ := fun k=>min (((N/D)*((2:ℝ)^k)^γ)^q) (((N/D)*((2:ℝ)^k)^γ)^(-1:ℝ))
  have hg := angular_crossing_sum (div_pos hN hD) hγ hq
  have hg0 (k : ℤ) : 0≤g k := by dsimp [g]; positivity
  have he (j : ℕ) : cappedRepresentative j=(2:ℝ)^(-(j:ℤ)) := by
    simp only [cappedRepresentative,zpow_neg,zpow_natCast,inv_pow]
  have hi : Function.Injective (fun j : ℕ=>-(j:ℤ)) := by
    intro a b hab
    exact_mod_cast neg_injective hab
  calc
    _≤∑'nt : ℕ,ENNReal.ofReal K*ENNReal.ofReal (g (-(nt:ℤ))) := by
      apply ENNReal.tsum_le_tsum
      intro nt
      have hb := scaled_capped_crossing_normalised
        (mul_pos hN (Real.rpow_pos_of_pos (cappedRepresentative_pos nt) γ)) hD (hx nt) hα
      apply hb.trans_eq
      rw [←ENNReal.ofReal_mul hK]
      congr 1
      dsimp [K,g,q]
      rw [he]
      congr 2 <;> congr 1 <;> ring
    _=ENNReal.ofReal K*(∑'nt : ℕ,ENNReal.ofReal (g (-(nt:ℤ)))) := ENNReal.tsum_mul_left
    _≤ENNReal.ofReal K*(∑'k : ℤ,ENNReal.ofReal (g k)) :=
      mul_le_mul' le_rfl (ENNReal.tsum_comp_le_tsum_of_injective hi (fun index => ENNReal.ofReal (g index)))
    _=ENNReal.ofReal K*ENNReal.ofReal (∑'k : ℤ,g k) := by
      rw [ENNReal.ofReal_tsum_of_nonneg hg0 hg.1]
    _≤ENNReal.ofReal K*ENNReal.ofReal (dyadicBalanceConstant (γ*q) γ) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hg.2)
    _=_ := by rw [←ENNReal.ofReal_mul hK]

end RVM
end
end
end OAI
