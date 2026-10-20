@[expose] public section

namespace CategoryTheory

namespace Functor

variable {C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ E : Type*}
  [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  [Category* D₁] [Category* D₂] [Category* D₃] [Category* D₄] [Category* E]

/-- Currying functors in four variables gives a fully faithful functor. -/
@[implicit_reducible]
def fullyFaithfulCurry₄ :
    (curry₄ : (C₁ × C₂ × C₃ × C₄ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E)).FullyFaithful :=
  currying₄.fullyFaithfulInverse

end Functor
end CategoryTheory
end
