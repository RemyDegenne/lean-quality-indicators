open Ordinal

open scoped NatOrdinal

@[expose] public noncomputable section

namespace ConwayRefinement.Standalone.PrincipalRVAlgebraicIndependence

universe u v

variable {K : Type u} [Field K]

open scoped Classical in
/-- **Berarducci's ordinal value** `v_J` [Ber00, Def. 5.2]: `0` on `J`, `1` on `(J + K) \ J`, and
otherwise the least order type of the support of a series congruent to `x` modulo `J + K`. -/
def ordinalValue (x : nonpos K) : NatOrdinal :=
  if MemJ x then 0
  else if IsNearConstant x then 1
  else sInf {o | ∃ c : nonpos K,
    IsNearConstant (x - c) ∧ NatOrdinal.of (ot (c : HahnSeries ℝ K)) = o}

end ConwayRefinement.Standalone.PrincipalRVAlgebraicIndependence
end
