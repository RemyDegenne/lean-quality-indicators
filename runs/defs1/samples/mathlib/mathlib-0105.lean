@[expose] public section

universe v u

noncomputable section

namespace CategoryTheory

open Category Limits Presieve

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

variable (C)

/-- If `J` is a precoverage that has isomorphisms and is stable under composition and
base change, it defines a pretopology. -/
@[simps toPrecoverage]
def Precoverage.toPretopology [Limits.HasPullbacks C] (J : Precoverage C) [J.HasIsos]
    [J.IsStableUnderBaseChange] [J.IsStableUnderComposition] : Pretopology C where
  __ := J
  has_isos X Y f hf := mem_coverings_of_isIso f
  pullbacks X Y f R hR := J.pullbackArrows_mem f hR
  transitive X R Ti hR hTi := by
    obtain ⟨ι, Z, g, rfl⟩ := R.exists_eq_ofArrows
    choose κ W p hp using fun ⦃Y⦄ (f : Y ⟶ X) hf ↦ (Ti f hf).exists_eq_ofArrows
    have : (Presieve.ofArrows Z g).bind Ti =
        .ofArrows (fun ij : Σ i, κ (g i) ⟨i⟩ ↦ W _ _ ij.2) (fun ij ↦ p _ _ ij.2 ≫ g ij.1) := by
      apply le_antisymm
      · rintro T u ⟨S, v, w, ⟨i⟩, hv, rfl⟩
        rw [hp] at hv
        obtain ⟨j⟩ := hv
        exact .mk <| Sigma.mk (β := fun i : ι ↦ κ (g i) ⟨i⟩) i j
      · rintro T u ⟨ij⟩
        use Z ij.1, p (g ij.1) ⟨ij.1⟩ ij.2, g ij.1, ⟨ij.1⟩
        rw [hp]
        exact ⟨⟨_⟩, rfl⟩
    rw [this]
    refine J.comp_mem_coverings (Y := fun (i : ι) (j : κ (g i) ⟨i⟩) ↦ W _ _ j)
      (g := fun i j ↦ p _ _ j) _ hR fun i ↦ ?_
    rw [← hp]
    exact hTi _ _

end CategoryTheory
end
end
