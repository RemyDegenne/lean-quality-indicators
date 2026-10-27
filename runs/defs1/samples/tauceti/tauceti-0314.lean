public section

open unitInterval Topology.Homotopy

universe u v

namespace TauCeti

variable {B : Type u} {K : Type v} [TopologicalSpace B] [TopologicalSpace K]

namespace MappingPathFiber

variable (f : C(B, K)) (k : K)

/-- Flattening identifies the two-constraint path fibre with the literal endpoint fibre. -/
def endpointHomeomorph :
    MappingPathFiber f k ≃ₜ {p : MappingPathSpace f // MappingPathSpace.endpoint f p = k} where
  toFun p := ⟨⟨p.val, p.property.1⟩,
    (MappingPathSpace.endpoint_apply f ⟨p.val, p.property.1⟩).trans p.property.2⟩
  invFun p := ⟨p.val.val, p.val.property,
    (MappingPathSpace.endpoint_apply f p.val).symm.trans p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_val).subtype_mk _

end MappingPathFiber
end TauCeti
end
