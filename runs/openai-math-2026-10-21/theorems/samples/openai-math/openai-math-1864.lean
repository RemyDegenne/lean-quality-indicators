namespace OAI

namespace RegularPointCoordinates

section

open Set Filter MeasureTheory Metric

open scoped Topology

theorem two_flow_evi_contraction {D : ℝ → ℝ → ℝ} {P Q : ℝ → ℝ} {K a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hD : ∀ a b : ℝ, 0 < a → 0 < b → ContinuousAt (Function.uncurry D) (a,b))
    (hP : ∀ a : ℝ, 0 < a → ContinuousAt P a)
    (hQ : ∀ a : ℝ, 0 < a → ContinuousAt Q a)
    (hI : ∀ a b s : ℝ, 0 < a → a ≤ b → 0 < s →
      (D b s-D a s)/2 ≤ ∫q in a..b, Q s-P q-(K/2)*D q s)
    (hJ : ∀ a b s : ℝ, 0 < a → a ≤ b → 0 < s →
      (D s b-D s a)/2 ≤ ∫q in a..b, P s-Q q-(K/2)*D s q) :
    D b b ≤ D a a*Real.exp (-2*K*(b-a)) := by
  have hc : ContinuousOn (fun t => D t t) (Icc a b) := fun t ht =>
    ((hD t t (ha.trans_le ht.1) (ha.trans_le ht.1)).comp (f := fun w : ℝ => (w,w))
      (continuousAt_id.prodMk continuousAt_id)).continuousWithinAt
  have hgr := le_gronwallBound_of_liminf_deriv_right_le (f' := fun t => -2*K*D t t)
    (K := -2*K) (ε := 0) hc (by
      intro t ht r hr
      have hh := two_flow_evi_frequent_slope (ha.trans_le ht.1) hD hP hQ hI hJ r hr
      simpa only [slope_def_field,div_eq_mul_inv,mul_comm] using hh)
    le_rfl (by intro t ht; simp only [add_zero]; exact le_rfl) b ⟨hab,le_rfl⟩
  simpa only [gronwallBound_ε0] using hgr

end
end RegularPointCoordinates
end OAI
