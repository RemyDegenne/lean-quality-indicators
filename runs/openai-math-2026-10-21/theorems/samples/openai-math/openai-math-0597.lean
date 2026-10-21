namespace OAI

universe uAlpha

noncomputable section

namespace Problem348

theorem not_HFree_of_anchor_body {n : ℕ} (B : BinaryMatrix n)
    (r c : IncreasingMap 64 n) (r₀ r₁ c₀ c₁ : Fin n)
    (hr : ∀ i, r.val i < r₀) (hr₀₁ : r₀ < r₁)
    (hc : ∀ j, c.val j < c₀) (hc₀₁ : c₀ < c₁)
    (hanchor : ∀ u v, B (r.val u) (c.val v) = anchor64 u v)
    (hrow₀ : ∀ v, B r₀ (c.val v) = decide (v.val = 0))
    (hrow₁ : ∀ v, B r₁ (c.val v) = decide (v.val = 1))
    (hcol₀ : ∀ u, B (r.val u) c₀ = decide (u.val = 0))
    (hcol₁ : ∀ u, B (r.val u) c₁ = decide (u.val = 1))
    (h₀₀ : B r₀ c₀ = true) (h₀₁ : B r₀ c₁ = false)
    (h₁₀ : B r₁ c₀ = true) (h₁₁ : B r₁ c₁ = true) :
    ¬ HFree fixedH B := by
  classical
  let rr := appendTwoIncreasing r r₀ r₁ hr hr₀₁
  let cc := appendTwoIncreasing c c₀ c₁ hc hc₀₁
  have hmem : (rr, cc) ∈ orderedCopies fixedH B := by
    simp only [orderedCopies, Finset.mem_filter, Finset.mem_univ, true_and]
    exact appendTwo_matches_fixedH B r c r₀ r₁ c₀ c₁ hanchor hrow₀ hrow₁
      hcol₀ hcol₁ h₀₀ h₀₁ h₁₀ h₁₁
  have hpos : 0 < copyCount fixedH B :=
    Finset.card_pos.mpr ⟨(rr, cc), hmem⟩
  exact Nat.ne_of_gt hpos

end Problem348
end
end OAI
