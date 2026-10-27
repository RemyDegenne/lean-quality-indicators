@[expose] public section

namespace Domain.Neighborhood

open NeighborhoodSystem

variable {α β γ δ : Type*}

namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- **Theorem 2.5(i) (Scott 1981, PRG-19) — the identity mapping `I_D`.** `X I_D Y
↔ X ⊆ Y`
(confined to `𝒟 × 𝒟`). It is approximable: (i) `Δ ⊆ Δ`; (ii) `X ⊆ Y`, `X ⊆ Y'`
give `X ⊆ Y ∩ Y'`
with witness `X`; (iii) is transitivity `X' ⊆ X ⊆ Y ⊆ Y'`. -/
def idMap (V : NeighborhoodSystem α) : ApproximableMap V V where
  rel X Y := V.mem X ∧ V.mem Y ∧ X ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨V.master_mem, V.master_mem, subset_rfl⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hXY⟩ ⟨_, hY', hXY'⟩
    exact ⟨hX, V.inter_mem hY hY' hX (Set.subset_inter hXY hXY'), Set.subset_inter hXY hXY'⟩
  mono := by
    rintro X X' Y Y' ⟨_, _, hXY⟩ hX'X hYY' hX' hY'
    exact ⟨hX', hY', (hX'X.trans hXY).trans hYY'⟩

end ApproximableMap
end Domain.Neighborhood
end
