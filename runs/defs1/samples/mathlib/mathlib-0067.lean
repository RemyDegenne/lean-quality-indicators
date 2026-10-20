@[expose] public section

namespace CategoryTheory

variable {C₀ C₁ C₂ C₃ : Type*} [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃]

open CategoryTheory.Functor

namespace Adjunction

section

variable {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {F₀₂ : C₀ ⥤ C₂}
  {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁} {G₂₀ : C₂ ⥤ C₀}
  (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁) (adj₀₂ : F₀₂ ⊣ G₂₀)

/-- A natural isomorphism `G₂₁ ⋙ G₁₀ ≅ G₂₀` involving right adjoint functors
induces a natural isomorphism `F₀₁ ⋙ F₁₂ ≅ F₀₂` between the corresponding
left adjoint functors. -/
@[simps! -isSimp]
def leftAdjointCompIso (e₀₁₂ : G₂₁ ⋙ G₁₀ ≅ G₂₀) :
    F₀₁ ⋙ F₁₂ ≅ F₀₂ :=
  (conjugateIsoEquiv adj₀₂ (adj₀₁.comp adj₁₂)).symm e₀₁₂.symm

end
end Adjunction
end CategoryTheory
end
