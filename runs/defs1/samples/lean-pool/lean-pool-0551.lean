@[expose] public section

open FiniteDimensional BrauerGroup Module groupCohomology

variable {F K : Type} [Field K] [Field F] [Algebra F K]

variable (X : BrauerGroup F)

variable [FiniteDimensional F K]

open groupCohomology

namespace GoodRep

variable {X : BrauerGroup F} (A : GoodRep K X)

open groupCohomology in
/-- The cohomology class attached to a good representative and a system of conjugating units. -/
def toH2 (x_ : Π σ, A.conjFactor σ) : H2 (galAct F K) :=
  H2π (galAct F K) <| cocyclesOfIsMulCocycle₂ (A.isMulCocycle₂ x_)

end GoodRep
end
