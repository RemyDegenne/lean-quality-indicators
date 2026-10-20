public section

namespace TauCeti

open Set Function Topology

open scoped Pointwise

variable (G : Type*) {X : Type*} [Group G] [MulAction G X]

variable {G}

theorem range_macbeathHom (U : Set X) :
    (macbeathHom G U).range = Subgroup.closure (macbeathGenerators G U) := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
    ← range_comp]
  simp only [Function.comp_def, macbeathHom_of, Subtype.range_coe]

end TauCeti
end
