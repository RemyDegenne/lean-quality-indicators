public section

namespace TauCeti

open Complex Metric Set

open scoped ComplexConjugate

/-- **The Schwarz--Pick conjugate** of a self-map `f` of the open unit disc at a point `a`:
`f` conjugated by the scalar Moebius formulas centred at `-a` on the source and at `f a` on the
target.  When `f` is a holomorphic self-map of the disc and `‖a‖ < 1` the conjugate is again a
holomorphic self-map of the disc, but now fixing the origin
(`differentiableOn_and_mapsTo_ball_and_apply_zero_schwarzPickConjugate`), so Schwarz's lemma
applies to it at `0`.  This is the construction shared by the finite and infinitesimal
Schwarz--Pick estimates and by the equality case of the finite estimate. -/
noncomputable def schwarzPickConjugate (f : ℂ → ℂ) (a : ℂ) : ℂ → ℂ :=
  (fun η => (η - f a) / (1 - (starRingEnd ℂ) (f a) * η)) ∘ f ∘
    fun ξ => (ξ - (-a)) / (1 - (starRingEnd ℂ) (-a) * ξ)

end TauCeti
end
