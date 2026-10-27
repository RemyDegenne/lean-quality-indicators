@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ProfiniteGrp

/-- The canonical homomorphism from a procyclic group into its power-quotient limit. -/
def toPowerQuotientLimit (G : ProfiniteGrp.{u}) (hG : IsProcyclic G)
    (S : Set Nat.Primes) : G ⟶ ProfiniteGrp.limit (powerQuotientDiagram G hG S) :=
  (ProfiniteGrp.limitConeIsLimit (powerQuotientDiagram G hG S)).lift
    (powerQuotientCone G hG S)

end ProfiniteGrp
end
