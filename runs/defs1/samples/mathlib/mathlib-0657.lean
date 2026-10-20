@[expose] public section

open Function Matrix

open scoped Nat

@[inherit_doc]
notation M " [⋀^" ι "]→L[" R "] " N:100 => ContinuousAlternatingMap R M N ι

namespace ContinuousAlternatingMap

section Module

variable {R A M N ι : Type*} [Semiring R] [Semiring A] [AddCommMonoid M] [AddCommMonoid N]
  [TopologicalSpace M] [TopologicalSpace N] [ContinuousAdd N] [Module A M] [Module A N] [Module R N]
  [ContinuousConstSMul R N] [SMulCommClass A R N]

/-- Linear map version of the map `toAlternatingMap`
associating to a continuous alternating map the corresponding alternating map. -/
@[simps -fullyApplied apply]
def toAlternatingMapLinear : (M [⋀^ι]→L[A] N) →ₗ[R] (M [⋀^ι]→ₗ[A] N) where
  toFun := toAlternatingMap
  map_add' := by simp
  map_smul' := by simp

end Module
end ContinuousAlternatingMap
end
