@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ProfiniteGrp

/-- Transport between the explicit power-quotient and residue limits, induced
by the generator-normalized comparison at exact-index levels. -/
noncomputable def powerQuotientLimitIsoResidue (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (g : G) (hg : IsTopologicalGenerator G g)
    (S : Set Nat.Primes)
    (hindex : ∀ n : Nat.PowerIndex S,
      (powerImage G hG n.val : Subgroup G).index = n.val) :
    ProfiniteGrp.limit (powerQuotientDiagram G hG S) ≅
      ProfiniteGrp.limit (residueDiagram.{u} S) :=
  IsLimit.conePointsIsoOfNatIso
    (ProfiniteGrp.limitConeIsLimit (powerQuotientDiagram G hG S))
    (ProfiniteGrp.limitConeIsLimit (residueDiagram.{u} S))
    (residuePowerQuotientNatIso G hG g hg S hindex).symm

end ProfiniteGrp
end
