namespace OAI

namespace PartitionPilot.Forcing.GroundMainPrefix

open SetFormula SetRealization

universe u

variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)

variable (unions : Realize M.sets SetFormula.union Fin.elim0)

variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

variable (first second : GroundLinkedMainStage M K Labels C D rD)

variable (step : GroundChronologicalMainTransition first.main second.main)

variable (coverage : step.CoversOldBirths)

theorem twoStage_indices :
    (twoStage pairing unions powers separation first second step coverage).indices = natSetCode 2 :=
  finiteMainIndexKey_range 2

end PartitionPilot.Forcing.GroundMainPrefix
end OAI
