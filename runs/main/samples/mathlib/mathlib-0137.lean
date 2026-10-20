@[expose] public section

open Module Filter

open scoped Topology Nat

noncomputable section

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M] (L : PeriodPair)

namespace PeriodPair

section weierstrassP

@[inherit_doc weierstrassP] scoped notation3 "℘[" L "]" => weierstrassP L

lemma weierstrassPExcept_add (l₀ : L.lattice) (z : ℂ) :
    ℘[L - l₀] z + (1 / (z - l₀.1) ^ 2 - 1 / l₀.1 ^ 2) = ℘[L] z := by
  trans ℘[L - l₀] z + ∑' i : L.lattice, if i = l₀.1 then (1 / (z - l₀.1) ^ 2 - 1 / l₀.1 ^ 2) else 0
  · simp
  rw [weierstrassPExcept, ← Summable.tsum_add]
  · congr with w; split_ifs <;> simp only [zero_add, add_zero, *]
  · exact ⟨_, L.hasSum_weierstrassPExcept _ _⟩
  · exact summable_of_hasFiniteSupport ((Set.finite_singleton l₀).subset (by simp))

end weierstrassP
end PeriodPair
end
end
