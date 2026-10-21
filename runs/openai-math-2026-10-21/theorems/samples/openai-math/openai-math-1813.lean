namespace OAI

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

namespace Percolation

universe u v

variable {V : Type u} {E : Type v}

open MeasureTheory Filter

section MarkedSearchTransfer

attribute [local instance] Classical.propDecidable Classical.decEq

theorem markedConnection_transfer (G : BondGraph V E) (Q : Finset E) (x : V)
    (d : ℕ) (hd : 0 < d) (hdeg : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d)
    (p q h : unitInterval) (hp : 0 < (p:ℝ)) (hpq : p ≤ q) (hq : (q:ℝ) < 1)
    (hh : 0 < (h:ℝ)) :
    markedConnectionPolynomial G Q x h q ≤
      Real.exp ((Real.sqrt ((d:ℝ)/2)/((p:ℝ)*(1-(q:ℝ)))) *
        Real.sqrt (Real.log (1/(h:ℝ))/(h:ℝ))*((q:ℝ)-(p:ℝ))) *
      markedConnectionPolynomial G Q x h p := by
  let H := markedConnectionPolynomial G Q x h
  have hdiff : Differentiable ℝ H := fun t => (hasDerivAt_bernoulliPolynomial Q _ t).differentiableAt
  apply exponential_transfer_of_deriv_bound H p q _ hdiff hpq
  intro t ht
  let r : unitInterval := ⟨t,⟨le_trans p.2.1 ht.1,le_trans ht.2 q.2.2⟩⟩
  have hr0 : 0 < t := lt_of_lt_of_le hp ht.1
  have hr1 : t < 1 := lt_of_le_of_lt ht.2 hq
  have HB := markedConnection_derivative_bound G Q x r h hr1 hh d hd hdeg
  have hH : 0 ≤ H t := by
    change 0 ≤ markedConnectionPolynomial G Q x h r
    rw [markedConnectionPolynomial_eq_tree]
    exact ProbeTree.successMass_nonneg r h _
  have hs : 0 ≤ Real.sqrt (Real.log (1/(h:ℝ))/(h:ℝ)) := Real.sqrt_nonneg _
  have hden : (p:ℝ)*(1-(q:ℝ)) ≤ t*(1-t) := by
    exact mul_le_mul ht.1 (by linarith [ht.2]) (sub_pos.mpr hq).le (by positivity)
  have hratio : Real.sqrt ((d:ℝ)/2)/(t*(1-t)) ≤
      Real.sqrt ((d:ℝ)/2)/((p:ℝ)*(1-(q:ℝ))) :=
    div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (mul_pos hp (sub_pos.mpr hq)) hden
  have hle : deriv H t ≤ (Real.sqrt ((d:ℝ)/2)/(t*(1-t)))*
      Real.sqrt (Real.log (1/(h:ℝ))/(h:ℝ))*H t := by
    have HBr : deriv H t ≤ ((Real.sqrt ((d:ℝ)/2)/(1-t))*
        Real.sqrt (Real.log (1/(h:ℝ))/(h:ℝ))*H t)/t := by
      apply (le_div_iff₀ hr0).mpr
      simpa only [mul_comm (deriv H t) t] using HB
    convert HBr using 1
    field_simp
  exact hle.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hratio hs) hH)

end MarkedSearchTransfer
end Percolation
end OAI
