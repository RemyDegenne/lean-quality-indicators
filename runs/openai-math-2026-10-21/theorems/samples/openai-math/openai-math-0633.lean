namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite

universe u v w uR

variable {R : Type uR} {A : Type u} {S : Type v}

variable [Fintype R] [Fintype A] [Fintype S]

variable (e : R → A → ScalarSiteExpansion.{v,w} S)

omit [Fintype R] [Fintype S] in
theorem forecastSiteMixture_factor_support
    {T D C H : A → ℝ} {L : ℝ≥0}
    (he : ∀ r a, (e r a).Bounds (T a) (D a) (C a) L (H a))
    (t : Σ r, ∀ a, (e r a).Term) (s : S)
    (r : ∀ a, ZMod ((e t.1 a).period (t.2 a)))
    (G : (A → ℝ) → ℂ) (χ : ℂ) (x : A → ℝ)
    (hx : ∃ a, H a ≤ |x a|) :
    (χ * G x) * siteFamilyFactor (e t.1) t.2 s r x = 0 := by
  rw [siteFamilyFactor_support (e t.1) (he t.1) t.2 s r x hx, mul_zero]

end Erdos3
end
end OAI
