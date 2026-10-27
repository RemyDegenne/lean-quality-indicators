universe u v w

open scoped NatOrdinal Topology

open Filter MvPolynomial HahnSeries HahnSeries.Nonpositive

public noncomputable section

namespace HahnSeries.Germ

variable {G : Type u} {K : Type v}

variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [Field K] [CharZero K]

local notation "ν" => (cantorBendixsonDegreeValuation (G := G) (R := K))

variable {ι : Type w} {wt : ι → NatOrdinal.{u}}
  {xg : ι → (cantorBendixsonDegreeValuation (G := G) (R := K)).AssociatedGraded}

variable (σ : LiftFamily wt xg)

namespace LimitOrdinalRelationAtCutoff

variable {σ} {α : NatOrdinal.{u}} (S : LimitOrdinalRelationAtCutoff σ α)

variable (hx : OrdinalGraded.IsMinimalSystem
  (DirectSum.rangeLof K
    (cantorBendixsonDegreeValuation (G := G) (R := K)).Component) wt xg)

/-- The part `α_{≥β}` of `α` at or above `β`. -/
def αGE : NatOrdinal := NatOrdinal.partGE S.β α

end LimitOrdinalRelationAtCutoff
end HahnSeries.Germ
end
