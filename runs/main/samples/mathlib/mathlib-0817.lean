@[expose] public section

variable {X Y Z α : Type*} [TopologicalSpace X]

open Set Filter

open scoped Topology

namespace LocallyConstant

section Indicator

variable {R : Type*} [One R] {U : Set X} (f : LocallyConstant X R)

variable (a : X)

variable {a}

@[to_additive]
theorem mulIndicator_of_notMem (hU : IsClopen U) (h : a ∉ U) : f.mulIndicator hU a = 1 :=
  Set.mulIndicator_of_notMem h _

end Indicator
end LocallyConstant
end
