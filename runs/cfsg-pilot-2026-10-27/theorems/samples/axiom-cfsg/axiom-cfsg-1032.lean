public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.AGLEmbedding.UnitaryLevi

open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K]

section Node

variable (h : UnitaryFieldData p f K) {r ε : ℕ} (a : ℕ) (ha : a + 2 ≤ r)

theorem nodeMap_inr_inr (c : Fin 2) :
    nodeMap (ε := ε) a ha (.inr (.inr c)) = .inr (.inr ⟨a + c, by have := c.2; omega⟩) := rfl

end Node
end CFSG.HardMathSupport.Curtis.UnitaryLevi
end
