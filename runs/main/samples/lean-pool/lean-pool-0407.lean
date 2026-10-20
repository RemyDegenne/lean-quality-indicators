@[expose] public section

noncomputable section

open Set Function MeasureTheory Filter

open scoped ContDiff Interval Topology

namespace NavierStokes.TransportPrimitive

universe u

section Shifted

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem iteratedFDeriv_pastIntegral_norm_le {a b M C : ℝ} {v : E}
    {f : ℝ × E → F} (hab : a ≤ b) (hf : ContDiff ℝ ∞ f)
    (hs : RadialAlias.RadiallySupported a b f) (n : ℕ)
    (hbound : ∀ s ∈ Icc a b, ∀ Y : E, ‖iteratedFDeriv ℝ n f (s, Y)‖ ≤ C) (z : ℝ × E) :
    ‖iteratedFDeriv ℝ n (pastIntegral M v f) z‖ ≤ C * (b - a) := by
  rw [iteratedFDeriv_pastIntegral hf hs]
  exact pastIntegral_norm_le hab (iteratedFDeriv_contDiff hf n).continuous
    (iteratedFDeriv_supported hs n) hbound z

end Shifted
end NavierStokes.TransportPrimitive
end
end
