public section

namespace TauCeti

open scoped BigOperators

attribute [local instance] IsConj.setoid

variable {G : Type*} [Group G]

namespace ClassData

variable (d : ClassData G)

section Executable

variable [DecidableRel (IsConj : G → G → Prop)]

variable [Fintype G]

section StructureConstants

@[simp]
theorem length_structureConstantTable : d.structureConstantTable.length = d.numClasses := by
  simp [structureConstantTable]

end StructureConstants
end Executable
end ClassData
end TauCeti
end
