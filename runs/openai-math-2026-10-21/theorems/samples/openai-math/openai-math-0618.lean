namespace OAI

section

section

open CategoryTheory Limits HomologicalComplex HomologicalComplex₂

namespace TotalProjection

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{0} C]

variable (K : HomologicalComplex₂ C c c)

@[reassoc (attr := simp)] lemma inclusion_projection (p q n : ℕ) (h : p+q=n) :
    K.ιTotal c p q n h ≫ projection K p q n = 𝟙 _ := by
  simp [projection]

end TotalProjection
end
end
end OAI
