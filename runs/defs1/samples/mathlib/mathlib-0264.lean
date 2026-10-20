@[expose] public section

noncomputable section

open scoped Topology Filter ENNReal NNReal

open Filter Asymptotics Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section Module

variable (𝕜)

variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]

/-- Line derivative of `f` at the point `x` in the direction `v`, if it exists.  Zero otherwise.

If the line derivative exists (i.e., `∃ f', HasLineDerivAt 𝕜 f f' x v`), then
`f (x + t v) = f x + t lineDeriv 𝕜 f x v + o (t)` when `t` tends to `0`.
-/
def lineDeriv (f : E → F) (x : E) (v : E) : F :=
  deriv (fun t ↦ f (x + t • v)) (0 : 𝕜)

end Module
end
end
