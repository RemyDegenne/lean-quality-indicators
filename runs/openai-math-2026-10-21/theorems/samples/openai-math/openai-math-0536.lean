namespace OAI

open Filter Set Topology

namespace DefocusingNLS

namespace RadialODEExpr

theorem iteratedDeriv_position (ν : ℂ) (n : ℕ) (f g : ℝ → ℂ) (L : ℝ)
    (hf : ∀ t, L < t → HasDerivAt f (g t) t)
    (hg : ∀ t, L < t → HasDerivAt g (eval f g t (acceleration ν n)) t)
    (k : ℕ) : ∀ t, L < t →
      iteratedDeriv k f t = eval f g t ((differentiate ν n)^[k] position) := by
  induction k with
  | zero =>
      intro t ht
      simp only [iteratedDeriv_zero, Function.iterate_zero, id_eq, eval]
  | succ k ih =>
      intro t ht
      have he : iteratedDeriv k f =ᶠ[𝓝 t]
          (fun s => eval f g s ((differentiate ν n)^[k] position)) := by
        filter_upwards [eventually_gt_nhds ht] with s hs
        exact ih s hs
      rw [iteratedDeriv_succ, he.deriv_eq]
      simpa only [Function.iterate_succ_apply'] using
        (hasDerivAt_eval ν n f g t (hf t ht) (hg t ht)
          ((differentiate ν n)^[k] position)).deriv

end RadialODEExpr
end DefocusingNLS
end OAI
