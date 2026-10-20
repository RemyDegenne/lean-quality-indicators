@[expose] public section

universe uO uK uΓ uΔ

namespace Valuation

theorem Integers.isEquiv
    {O : Type uO} {K : Type uK} {Γ₀ : Type uΓ} {Δ₀ : Type uΔ}
    [CommRing O] [Field K] [Algebra O K]
    [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Δ₀]
    {v : Valuation K Γ₀} {w : Valuation K Δ₀}
    (hv : v.Integers O) (hw : w.Integers O) : v.IsEquiv w := by
  apply Valuation.isEquiv_of_val_le_one
  intro x
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := hv.exists_of_le_one hx
    exact hw.map_le_one a
  · intro hx
    obtain ⟨a, rfl⟩ := hw.exists_of_le_one hx
    exact hv.map_le_one a

end Valuation
end
