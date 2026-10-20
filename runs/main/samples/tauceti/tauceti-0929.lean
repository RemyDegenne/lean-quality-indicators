public section

namespace TauCeti

open Metric Set Topology

variable {X : Type*} [PseudoMetricSpace X] {s : Set X}

theorem isUniformlyLocallyConnected_iff_exists_isConnected_diam_le :
    IsUniformlyLocallyConnected s ↔ ∀ ε > 0, ∃ δ > 0, ∀ a ∈ s, ∀ b ∈ s, dist a b < δ →
      ∃ C ⊆ s, IsConnected C ∧ a ∈ C ∧ b ∈ C ∧ Bornology.IsBounded C ∧ diam C ≤ ε := by
  refine ⟨fun h ε hε => h.exists_isConnected_diam_le hε,
    fun h => isUniformlyLocallyConnected_def.mpr fun ε hε => ?_⟩
  obtain ⟨δ, hδ, hjoin⟩ := h ε hε
  refine ⟨δ, hδ, fun a ha b hb hab => ?_⟩
  obtain ⟨C, hCs, hCconn, hCa, hCb, hCbdd, hCdiam⟩ := hjoin a ha b hb hab
  exact ⟨C, hCs, hCconn, hCa, hCb,
    fun x hx y hy => (dist_le_diam_of_mem hCbdd hx hy).trans hCdiam⟩

end TauCeti
end
