namespace OAI

noncomputable section

open Set MeasureTheory

open scoped Pointwise ENNReal

namespace PeriodicTilingThree.PeriodicVolume

variable {d : ℕ}

@[simp] theorem mem_assembly {C : Set (Space d)} {K : Space d → Set (Space d)}
    {x : Space d} : x ∈ assembly C K ↔ ∃ c : C, x - (c : Space d) ∈ K c := by
  simp only [assembly, mem_iUnion, mem_translate]

end PeriodicTilingThree.PeriodicVolume
end
end OAI
