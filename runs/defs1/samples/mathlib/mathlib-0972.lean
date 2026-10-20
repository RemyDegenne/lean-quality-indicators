@[expose] public section

namespace CategoryTheory

open Category Limits Preadditive

variable (C : Type*) [Category* C] [Abelian C]

namespace ShortComplex

namespace SnakeInput

attribute [instance] epi_L₁_g

attribute [instance] mono_L₂_f

variable {C}

variable (S : SnakeInput C)

variable (S₁ S₂ S₃ : SnakeInput C)

variable {S₁ S₂ S₃}

/-- The functor which sends `S : SnakeInput C` to `S.L₁'` which is
`S.L₀.X₂ ⟶ S.L₀.X₃ ⟶ S.L₃.X₁`. -/
@[simps]
noncomputable def functorL₁' : SnakeInput C ⥤ ShortComplex C where
  obj S := S.L₁'
  map f :=
    { τ₁ := f.f₀.τ₂
      τ₂ := f.f₀.τ₃
      τ₃ := f.f₃.τ₁
      comm₁₂ := f.f₀.comm₂₃
      comm₂₃ := (naturality_δ f).symm }

end SnakeInput
end ShortComplex
end CategoryTheory
end
