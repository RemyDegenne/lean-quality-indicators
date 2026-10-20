@[expose] public section

universe v u

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

namespace ShortComplex

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

variable {S}

variable (S)

variable {S}

variable (S)

variable {S}

variable (S)

variable (S₁ S₂)

variable {S₁ S₂}

variable {S}

variable (S)

variable {S}

variable (S)

variable {S}

set_option backward.defeqAttrib.useBackward true in
lemma HomologyData.right_homologyIso_eq_left_homologyIso_trans_iso
    (h : S.HomologyData) [S.HasHomology] :
    h.right.homologyIso = h.left.homologyIso ≪≫ h.iso := by
  suffices h.iso = h.left.homologyIso.symm ≪≫ h.right.homologyIso by
    rw [this, Iso.self_symm_id_assoc]
  ext
  dsimp
  rw [← leftRightHomologyComparison'_fac, leftRightHomologyComparison'_eq]

end ShortComplex
end CategoryTheory
end
