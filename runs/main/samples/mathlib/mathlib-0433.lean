@[expose] public section

variable {X Y Z α : Type*} [TopologicalSpace X]

open Set Filter

open scoped Topology

namespace LocallyConstant

section Indicator

variable {R : Type*} [One R] {U : Set X} (f : LocallyConstant X R)

variable (a : X)

open scoped Classical in
@[to_additive]
theorem mulIndicator_apply_eq_if (hU : IsClopen U) :
    mulIndicator f hU a = if a ∈ U then f a else 1 :=
  Set.mulIndicator_apply U f a

end Indicator
end LocallyConstant
end
