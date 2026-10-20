public section

noncomputable section

namespace TauCeti

section

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommMonoid F] [Module ℝ F]

variable (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) {f : E → EReal} {x : E} {y : F} {r : ℝ}

/-- The *subgradient image* `∂f(s) = ⋃ x ∈ s, ∂f(x)` of a set `s` with respect to the pairing
`B`: the set of all subgradients of `f` at points of `s`. -/
def subgradientImage (f : E → EReal) (s : Set E) : Set F :=
  ⋃ x ∈ s, subdifferential B f x

end
end TauCeti
end
end
