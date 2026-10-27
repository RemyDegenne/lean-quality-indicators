public section

open unitInterval

universe u v u' v' u'' v''

namespace TauCeti

variable {B : Type u} {K : Type v} [TopologicalSpace B] [TopologicalSpace K]

namespace MappingPathSpace

variable (f : C(B, K))

/-- The constant-path inclusion is a homotopy equivalence, inverse to projection. -/
def homotopyEquiv : ContinuousMap.HomotopyEquiv B (MappingPathSpace f) where
  toFun := incl f
  invFun := proj f
  left_inv := by rw [proj_comp_incl]
  right_inv := ⟨shrinkHomotopy f⟩

end MappingPathSpace
end TauCeti
end
