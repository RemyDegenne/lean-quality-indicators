public section

noncomputable section

open Set Set.Notation Topology

namespace CompactCoherentification

@[inherit_doc]
scoped notation "𝐤" X:max => CompactCoherentification X

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

lemma continuous_mk_comp_iff_of_compactSpace [CompactSpace X] {f : X → Y} :
    Continuous ((CompactCoherentification.mk Y) ∘ f) ↔ Continuous f := by
  rw [continuous_rng_of_compactSpace, ← Function.comp_assoc, Equiv.symm_comp_self, Function.id_comp]

end CompactCoherentification
end
end
