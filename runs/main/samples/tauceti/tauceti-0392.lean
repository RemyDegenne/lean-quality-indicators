public section

namespace TauCeti

open Equiv

theorem youngSubgroup_eq_fiberSubgroup {n : ℕ} (μ : n.Partition) :
    youngSubgroup μ = fiberSubgroup (youngBlock μ) := by
  ext σ
  rw [mem_youngSubgroup_iff, mem_fiberSubgroup]
  simp only [funext_iff, Function.comp_apply]

end TauCeti
end
