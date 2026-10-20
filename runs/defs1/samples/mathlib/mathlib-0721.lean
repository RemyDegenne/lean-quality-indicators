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

/-- Given a morphism `φ : S₁ ⟶ S₂` of short complexes and homology data `h₁` and `h₂`
for `S₁` and `S₂` respectively, this is the induced homology map `h₁.left.H ⟶ h₁.left.H`. -/
def homologyMap' (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData) :
    h₁.left.H ⟶ h₂.left.H := leftHomologyMap' φ _ _

end ShortComplex
end CategoryTheory
end
