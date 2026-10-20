public section

open unitInterval Topology.Homotopy

universe u v

namespace TauCeti

variable {B : Type u} {K : Type v} [TopologicalSpace B] [TopologicalSpace K]

/-- Forget the redundant source point to identify a constant-map fibre with native paths. -/
def mappingPathFiberConstHomeomorphPath (b k : K) :
    MappingPathFiber (ContinuousMap.const Unit b) k ≃ₜ Path b k where
  toFun p := ⟨p.val.2, p.property.1, p.property.2⟩
  invFun γ := ⟨((), γ.toContinuousMap), γ.source, γ.target⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl
  right_inv _ := rfl
  continuous_toFun := continuous_induced_rng.2 continuous_subtype_val.snd
  continuous_invFun := (continuous_const.prodMk continuous_induced_dom).subtype_mk _

end TauCeti
end
