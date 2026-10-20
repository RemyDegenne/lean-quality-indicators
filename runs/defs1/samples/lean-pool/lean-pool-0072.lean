noncomputable section

attribute [local instance low] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [local instance low] AddSubgroupClass.instZModModule

namespace ConnesRigidity

section

open Set Submodule MeasureTheory

open scoped ENNReal Topology

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def splitCharacterL2 (d : D) : Lp ℂ 2 productHaar :=
  ContinuousMap.toLp 2 productHaar ℂ (splitComplexCharacter d)

end
end ConnesRigidity
end
