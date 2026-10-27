noncomputable section

attribute [local instance low] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [local instance low] AddSubgroupClass.instZModModule

namespace ConnesRigidity

section

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def fourthRootCharacter : PontryaginDual (Multiplicative (ZMod 4)) where
  toMonoidHom := fourthRootMonoidCharacter
  continuous_toFun := continuous_of_discreteTopology

end
end ConnesRigidity
end
