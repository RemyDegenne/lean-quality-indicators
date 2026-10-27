@[expose] public section

noncomputable section

open scoped Topology Filter ENNReal NNReal

open Filter Asymptotics Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section Module

variable (𝕜)

variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]

/-- Line derivative of `f` at the point `x` in the direction `v` within the set `s`, if it exists.
Zero otherwise.

If the line derivative exists (i.e., `∃ f', HasLineDerivWithinAt 𝕜 f f' s x v`), then
`f (x + t v) = f x + t lineDerivWithin 𝕜 f s x v + o (t)` when `t` tends to `0` and `x + t v ∈ s`.
-/
def lineDerivWithin (f : E → F) (s : Set E) (x : E) (v : E) : F :=
  derivWithin (fun t ↦ f (x + t • v)) ((fun t ↦ x + t • v) ⁻¹' s) (0 : 𝕜)

end Module
end
end
