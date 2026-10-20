@[expose] public section

noncomputable section

open Set Filter TopologicalSpace Topology

open scoped ENNReal

variable {α : Type*} [TopologicalSpace α]

namespace EReal

theorem tendsto_nhds_top_iff_real {α : Type*} {m : α → EReal} {f : Filter α} :
    Tendsto m f (𝓝 ⊤) ↔ ∀ x : ℝ, ∀ᶠ a in f, ↑x < m a :=
  nhds_top_basis.tendsto_right_iff.trans <| by simp only [true_implies, mem_Ioi]

end EReal
end
end
