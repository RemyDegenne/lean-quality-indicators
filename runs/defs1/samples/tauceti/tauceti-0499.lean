public section

open DirectSum MulOpposite

namespace TauCeti

universe uR uA uM uP uQ uS uT

section Cocycle

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A]
  {P : Type uP} {Q : Type uQ} {S : Type uS} {ind : P → ℤ} {indQ : Q → ℤ} {indS : S → ℤ}
  [Fintype P] [Fintype Q] [Fintype S]
  {𝒜 : ℤ → Submodule R A} {d : A →ₗ[R] A}

namespace ContinuationCocycle

variable {mP : TwistingCocycle 𝒜 d P ind} {mQ : TwistingCocycle 𝒜 d Q indQ}
  {mS : TwistingCocycle 𝒜 d S indS}

variable [GradedAlgebra 𝒜]

/-- The matrix product of continuation cocycles `mP → mQ` and `mQ → mS`, a continuation cocycle
`mP → mS`. -/
def comp (h : IsDGAlgebra 𝒜 d) (ν₁ : ContinuationCocycle mP mQ) (ν₂ : ContinuationCocycle mQ mS) :
    ContinuationCocycle mP mS where
  ν := Matrix.of ν₁.ν * Matrix.of ν₂.ν
  mem_graded := matMul_mem_graded ν₁.ν ν₂.ν ν₁.mem_graded ν₂.mem_graded
  continuation := continuation_matMul ν₁.ν ν₂.ν h mP.m mQ.m mS.m ν₁.mem_graded ν₁.continuation
    ν₂.continuation

end ContinuationCocycle
end Cocycle
end TauCeti
end
