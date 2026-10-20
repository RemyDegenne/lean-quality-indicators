@[expose] public section

open Real

variable {E : Type*} [NormedAddCommGroup E]

section NormedSpace

variable [NormedSpace ℝ E] {φ ψ : ℝ → ℝ} {s : Set E} {m : ℝ} {f g : E → ℝ}

/-- A function `f` from a real normed space is `m`-strongly convex if it is uniformly convex with
modulus `φ(r) = m / 2 * r ^ 2`.

In an inner product space, this is equivalent to `x ↦ f x - m / 2 * ‖x‖ ^ 2` being convex. -/
def StrongConvexOn (s : Set E) (m : ℝ) : (E → ℝ) → Prop :=
  UniformConvexOn s fun r ↦ m / (2 : ℝ) * r ^ 2

end NormedSpace
end
