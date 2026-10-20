@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ProfiniteGrp

/-- Turn an IsLimit proof into a continuous group equivalence. The only
assumption here is the explicitly supplied limit certificate. -/
noncomputable def continuousMulEquivPowerQuotientLimitOfIsLimit
    (G : ProfiniteGrp.{u}) (hG : IsProcyclic G) (S : Set Nat.Primes)
    (hlimit : IsLimit (powerQuotientCone G hG S)) :
    G ≃ₜ* ProfiniteGrp.limit (powerQuotientDiagram G hG S) := by
  let iso := IsLimit.conePointUniqueUpToIso hlimit
    (ProfiniteGrp.limitConeIsLimit (powerQuotientDiagram G hG S))
  exact { CompHausLike.homeoOfIso ((forget₂ ProfiniteGrp Profinite).mapIso iso) with
    map_mul' := map_mul iso.hom.hom }

end ProfiniteGrp
end
