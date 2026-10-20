@[expose] public section

noncomputable section

open Filter Set

open scoped SetRel Uniformity Topology

universe u v w

namespace CauchyFilter

section

variable {α : Type u} [UniformSpace α]

variable {β : Type v}

variable [UniformSpace β]

theorem inseparable_iff_of_le_nhds {f g : CauchyFilter α} {a b : α}
    (ha : f.1 ≤ 𝓝 a) (hb : g.1 ≤ 𝓝 b) : Inseparable a b ↔ Inseparable f g := by
  rw [← tendsto_id'] at ha hb
  rw [inseparable_iff, (ha.comp tendsto_fst).inseparable_iff_uniformity (hb.comp tendsto_snd)]
  simp only [Function.comp_apply, id_eq, Prod.mk.eta, ← Function.id_def, tendsto_id']

end
end CauchyFilter
end
end
