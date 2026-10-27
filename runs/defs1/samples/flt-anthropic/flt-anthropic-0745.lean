namespace P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent

set_option autoImplicit false

set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve

namespace FltWs11

namespace RoadB

namespace SecB

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve

local notation "ℤS" => Spec (CommRingCat.of ℤ)

local notation "Qb" => AlgebraicClosure ℚ

def pushAlong {X Y T : Scheme.{0}} {gX : X ⟶ ℤS} {gY : Y ⟶ ℤS} (k : X ⟶ Y) (hk : k ≫ gY = gX)
    {t : T ⟶ ℤS} (s : SchemeHomOver t gX) : SchemeHomOver t gY :=
  ⟨s.1 ≫ k, by rw [Category.assoc, hk, s.2]⟩

end SecB
end RoadB
end FltWs11
end P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent
