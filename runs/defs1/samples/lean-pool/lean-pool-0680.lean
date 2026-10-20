@[expose] public section

universe u

open scoped Cardinal

open ContinuousLinearMap

namespace SNumbers

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

variable {W X Y Z : Type u}

variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]

variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]

variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- An `s`-number sequence is **surjective** if pre-composition with any
metric surjection leaves it unchanged: `sₙ(S ∘ Q) = sₙ(S)`. -/
def Surjective (s : Family 𝕜) : Prop :=
  ∀ {W X Y : Type u} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
      [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
      (S : X →L[𝕜] Y) (Q : W →L[𝕜] X), IsMetricSurjection Q → ∀ n : ℕ,
    s (S.comp Q) n = s S n

end SNumbers
end
