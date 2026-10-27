@[expose] public section

open scoped Pointwise

namespace Supernatural

noncomputable section

variable (A : Type*) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]

/-- Inclusion of an additive subgroup, with multiplicative type tags. -/
def multiplicativeSubgroupInclusion (B : AddSubgroup A) :
    Multiplicative B →ₜ* Multiplicative A where
  toFun b := Multiplicative.ofAdd b.toAdd.1
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_of_discreteTopology

end
end Supernatural
end
