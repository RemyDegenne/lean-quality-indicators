public section

open Set

namespace ENat

variable {ι : Sort*} {f : ι → ℕ} {s : Set ℕ}

variable {f : ι → ℕ∞} {s : Set ℕ∞}

variable {ι κ : Sort*} {f g : ι → ℕ∞} {s : Set ℕ∞} {a : ℕ∞}

theorem sub_iInf : (a - ⨅ i, f i) = ⨆ i, a - f i := by
  refine eq_of_forall_ge_iff fun c => ?_
  rw [tsub_le_iff_right, add_comm, iInf_add]
  simp [tsub_le_iff_right, add_comm]

end ENat
end
