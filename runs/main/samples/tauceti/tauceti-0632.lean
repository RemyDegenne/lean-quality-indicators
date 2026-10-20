public section

open Set

open scoped Interval

namespace TauCeti.Contour

theorem argumentPrinciple_nullHomologous_of_analyticOnNhd {f : ℂ → ℂ} {S : Finset ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U) (hzeros : ∀ z ∈ U, f z = 0 → z ∈ S)
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : IsPiecewiseC1On γ a b)
    (hγU : ∀ t ∈ uIcc a b, γ t ∈ U) (hclosed : γ a = γ b)
    (hγoff : ∀ t ∈ uIcc a b, f (γ t) ≠ 0) (hnull : IsNullHomologous γ a b U) :
    ∫ t in a..b, deriv γ t • logDeriv f (γ t)
      = 2 * (Real.pi : ℂ) * Complex.I *
          ∑ z ∈ S, windingNumber γ a b z * (analyticOrderNatAt f z : ℂ) := by
  classical
  -- Discard from `S` the points where `f` does not vanish: their order is `0`, so the sum is
  -- unchanged, and what is left is a set the curve does avoid.
  rw [← Finset.sum_subset (Finset.filter_subset (f · = 0) S) fun z _ hz => ?_]
  · refine argumentPrinciple_nullHomologous (S := S.filter (f · = 0))
      (ord := fun z => (analyticOrderNatAt f z : ℤ)) hU
      (fun z hzU hzS => ⟨hf z hzU, fun h => hzS (Finset.mem_filter.mpr ⟨hzeros z hzU h, h⟩)⟩)
      (fun s _ hsU => (hf s hsU).meromorphicAt) (fun s _ hsU => ?_) hγ hγU hclosed
      (fun t ht hmem => hγoff t ht (Finset.mem_filter.mp hmem).2) hnull
    -- For an analytic function the meromorphic order is the analytic one, which is finite here.
    rw [(hf s hsU).meromorphicOrderAt_eq,
      ← Nat.cast_analyticOrderNatAt (analyticOrderAt_ne_top_of_zeros_subset hU hsU hzeros)]
    simp
  · have : analyticOrderNatAt f z = 0 := by
      by_contra h
      exact hz (Finset.mem_filter.mpr ⟨‹z ∈ S›, apply_eq_zero_of_analyticOrderNatAt_ne_zero h⟩)
    simp [this]

end TauCeti.Contour
end
