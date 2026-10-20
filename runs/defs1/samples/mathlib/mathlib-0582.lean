@[expose] public section

namespace CategoryTheory

open Category Limits

variable {C : Type*} [Category* C] [Preadditive C]
  {X₁ X₂ X₃ X₄ : C} [HasBinaryBiproduct X₂ X₃]

section Pullback

variable {fst : X₁ ⟶ X₂} {snd : X₁ ⟶ X₃} {f : X₂ ⟶ X₄} {g : X₃ ⟶ X₄}

/-- The limit kernel fork attached to a pullback square. -/
noncomputable def IsPullback.isLimitKernelFork (h : IsPullback fst snd f g) :
    IsLimit h.kernelFork :=
  h.isLimitEquivIsLimitKernelFork h.isLimit

end Pullback
end CategoryTheory
end
