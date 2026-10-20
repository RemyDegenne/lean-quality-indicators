@[expose] public section

open CategoryTheory Limits

noncomputable section

namespace CategoryTheory.EquivalenceRelation

universe v u

variable {C : Type u} [Category.{v, u} C]
  {R X : C} {p₁ p₂ : R ⟶ X}

lemma isIso_symmetry (h : CategoryTheory.EquivalenceRelation p₁ p₂) :
    IsIso h.s := by
  have hs : h.s ≫ h.s = 𝟙 R := by
    apply h.toJointlyMono₂.right_cancellation
    · rw [Category.assoc, h.symmetry₁, h.symmetry₂, Category.id_comp]
    · rw [Category.assoc, h.symmetry₂, h.symmetry₁, Category.id_comp]
  exact ⟨⟨h.s, hs, hs⟩⟩

end CategoryTheory.EquivalenceRelation
end
end
