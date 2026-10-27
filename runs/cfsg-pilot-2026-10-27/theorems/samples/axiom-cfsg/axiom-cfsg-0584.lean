public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[simp] theorem projOrthToProjSim_toProj (t : OGroup Q) :
    projOrthToProjSim Q (toProj Q t) = QuotientGroup.mk (orthToSim Q t) :=
  rfl

end CFSG.OddStandard.SmallF3.Omega
end
