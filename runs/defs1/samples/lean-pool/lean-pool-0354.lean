@[expose] public section

open scoped ComplexOrder

namespace Matrix

variable {n 𝕜 : Type _} [Fintype n]

variable [Field 𝕜] [StarRing 𝕜] [DecidableEq n]

section ConjKronecker

variable {n p 𝕜 : Type _} [RCLike 𝕜]

/-- Entrywise conjugate of a unitary matrix as a unitary. -/
def _root_.Matrix.unitaryGroup.conj [Fintype n] [DecidableEq n]
    (U : unitaryGroup n 𝕜) :
    unitaryGroup n 𝕜 :=
  ⟨(U : Matrix n n 𝕜)ᴴᵀ, Matrix.unitaryGroup.conj_mem U⟩

end ConjKronecker
end Matrix
end
