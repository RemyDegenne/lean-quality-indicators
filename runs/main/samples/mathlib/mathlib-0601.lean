public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (f : 𝕜 →ᵃ[𝕜] E) {a b : E} {L : Filter (𝕜 × 𝕜)} {s : Set 𝕜} {x : 𝕜}

namespace AffineMap

protected theorem derivWithin (hs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin f s x = f.linear 1 :=
  f.hasDerivWithinAt.derivWithin hs

end AffineMap
end
