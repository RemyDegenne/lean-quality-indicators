namespace OAI

section

namespace PerfectCompleteness.ProjectedCallRestriction

open RecursiveSpaces TreeSourceSpaces HierarchicalArrays PointwiseSpaces

open UniqueGamesTheorem.Foundations.Games

open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n t oldCalls enlargedCalls : Nat}

@[simp] theorem rawRestrict_calls (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (e : Fin oldCalls → Fin enlargedCalls)
    (block : ChildBlockCardinality.Raw enlargedCalls rows slots) (call : Fin oldCalls) :
    (rawRestrict rows slots e block).1 call = block.1 (e call) := rfl

end
end PerfectCompleteness.ProjectedCallRestriction
end
end OAI
