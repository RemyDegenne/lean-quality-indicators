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

/-- When a short complex has homology, its homology can be computed using
any right homology data. -/
noncomputable def RightHomologyData.homologyIso (h : S.RightHomologyData) [S.HasHomology] :
    S.homology ≅ h.H := S.rightHomologyIso.symm ≪≫ h.rightHomologyIso

end ShortComplex
end CategoryTheory
end
