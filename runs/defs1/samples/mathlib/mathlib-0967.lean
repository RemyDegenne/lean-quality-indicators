@[expose] public section

namespace CategoryTheory

open Category Limits

namespace ShortComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable {S}

section

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData)

namespace LeftHomologyMapData

variable {φ h₁ h₂}

variable (S)

set_option backward.isDefEq.respectTransparency.types false in
/-- When both maps `S.f` and `S.g` of a short complex `S` are zero, this is the left homology map
data (for the identity of `S`) which relates the left homology data `ofZeros` and
`ofIsColimitCokernelCofork`. -/
@[simps]
def compatibilityOfZerosOfIsColimitCokernelCofork (hf : S.f = 0) (hg : S.g = 0)
    (c : CokernelCofork S.f) (hc : IsColimit c) :
    LeftHomologyMapData (𝟙 S) (LeftHomologyData.ofZeros S hf hg)
      (LeftHomologyData.ofIsColimitCokernelCofork S hg c hc) where
  φK := 𝟙 _
  φH := c.π

end LeftHomologyMapData
end
end ShortComplex
end CategoryTheory
end
