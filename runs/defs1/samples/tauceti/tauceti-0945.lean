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

/-- The Kronecker matrix, as a continuation cocycle from `m` to itself, for a differential with
`d 1 = 0`. -/
def refl [DecidableEq P] (hd : d 1 = 0) (m : TwistingCocycle 𝒜 d P ind) :
    ContinuationCocycle m m where
  ν := (1 : Matrix P P A)
  mem_graded := kronecker_mem_graded
  continuation := continuation_kronecker m.m hd

end ContinuationCocycle
end Cocycle
end TauCeti
end
