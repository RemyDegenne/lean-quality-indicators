@[expose] public section

open Filter MeasureTheory Set

open scoped ENNReal SchwartzMap Topology

namespace QuadraticCarleson

namespace HilbertPrincipalValueClosure

open HilbertFiniteTruncationWeakOneOne OscillatoryReduction

theorem ae_forall_lacunary_exists_quadraticPrincipalValue
    {C : ℝ≥0∞} (hweak : HasUniformHilbertMaximalWeakBound C) (f : L0Infinity) :
    ∀ᵐ x, ∀ m : ℤ, ∃ z : ℂ, HasQuadraticPrincipalValue (dyadicModulation m) f x z := by
  filter_upwards [ae_forall_real_exists_quadraticPrincipalValue hweak f] with x hx
  exact fun m ↦ hx (dyadicModulation m)

end HilbertPrincipalValueClosure
end QuadraticCarleson
end
