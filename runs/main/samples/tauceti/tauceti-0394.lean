public section

open Filter Set Topology

namespace Flow

variable {α : Type*} [TopologicalSpace α]

section Conjugacy

variable {β : Type*} [TopologicalSpace β]
  {φ : _root_.Flow ℝ α} {ψ : _root_.Flow ℝ β}

theorem _root_.Homeomorph.map_mem_unstableSet_iff
    (e : α ≃ₜ β) (hconj : _root_.Flow.IsSemiconjugacy e φ ψ) {x : α} {y : α} :
    e y ∈ unstableSet ψ (e x) ↔ y ∈ unstableSet φ x := by
  exact e.isInducing.map_mem_unstableSet_iff hconj

end Conjugacy
end Flow
end
