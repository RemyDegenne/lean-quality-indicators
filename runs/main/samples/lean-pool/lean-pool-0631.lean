universe u v w

open scoped NatOrdinal Topology

open MvPolynomial HahnSeries HahnSeries.Nonpositive DirectSum OrdinalGraded

public noncomputable section

namespace HahnSeries.Germ

variable {G : Type u} {K : Type v}

variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [Field K] [CharZero K]

local notation "ν" => (cantorBendixsonDegreeValuation (G := G) (R := K))

variable {ι : Type w} {wt : ι → NatOrdinal.{u}}
  {xg : ι → (cantorBendixsonDegreeValuation (G := G) (R := K)).AssociatedGraded}

namespace LimitOrdinalRelationAtCutoff

variable {σ : LiftFamily wt xg} {α : NatOrdinal.{u}}
  (S : HahnSeries.Germ.LimitOrdinalRelationAtCutoff σ α)

variable (hx : OrdinalGraded.IsMinimalSystem
  (DirectSum.rangeLof K (cantorBendixsonDegreeValuation (G := G) (R := K)).Component) wt xg)

include S hx

theorem α_constantCoeff : α.constantCoeff = 0 := by
  have h := congrArg NatOrdinal.constantCoeff S.hdegHD
  rw [NatOrdinal.constantCoeff_add, NatOrdinal.constantCoeff_nsmul, S.vars_limit _ S.mem,
    mul_zero, add_zero] at h
  rw [← h, ← NatOrdinal.partGE_eq_self_of_forall_le S.degHD_terms,
    NatOrdinal.constantCoeff_partGE (S.β_ne_zero hx)]

end LimitOrdinalRelationAtCutoff
end HahnSeries.Germ
end
