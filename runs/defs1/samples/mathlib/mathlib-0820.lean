@[expose] public section

namespace CategoryTheory

open Category Limits

namespace ShortComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable {S}

variable (S)

variable (S₁ S₂)

variable {S₁ S₂}

/-- An isomorphism of short complexes `S₁ ≅ S₂` induces an isomorphism on the `Q` fields
of right homology data of `S₁` and `S₂`. -/
@[simps]
def opcyclesMapIso' (e : S₁ ≅ S₂) (h₁ : S₁.RightHomologyData)
    (h₂ : S₂.RightHomologyData) : h₁.Q ≅ h₂.Q where
  hom := opcyclesMap' e.hom h₁ h₂
  inv := opcyclesMap' e.inv h₂ h₁
  hom_inv_id := by rw [← opcyclesMap'_comp, e.hom_inv_id, opcyclesMap'_id]
  inv_hom_id := by rw [← opcyclesMap'_comp, e.inv_hom_id, opcyclesMap'_id]

end ShortComplex
end CategoryTheory
end
