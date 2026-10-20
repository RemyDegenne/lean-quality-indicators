@[expose] public section

universe w v u

namespace CategoryTheory

open Abelian Limits ZeroObject

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace ShortComplex

namespace ShortExact

variable {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ)

include hS

lemma hasProjectiveDimensionLT_X₃_iff (n : ℕ) (h₂ : Projective S.X₂) :
    HasProjectiveDimensionLT S.X₃ (n + 2) ↔ HasProjectiveDimensionLT S.X₁ (n + 1) :=
  ⟨fun _ ↦ hS.hasProjectiveDimensionLT_X₁ (n + 1) inferInstance inferInstance,
    fun _ ↦ hS.hasProjectiveDimensionLT_X₃ (n + 1) inferInstance inferInstance⟩

end ShortExact
end ShortComplex
end CategoryTheory
end
