namespace OAI

section

namespace SharpLogRamsey.TreeShapes

open BinaryTree Finset

open scoped Classical

lemma boundedEncode_injective (N : ℕ) (S : Finset (BinaryTree Unit))
    (hS : ∀ t∈S,t.numNodes≤N) : Function.Injective (boundedEncode N S hS) := by
  intro s t he
  have hh := congrArg Subtype.val he
  exact Subtype.ext (prefix_free s.val t.val _ _ hh).1

end SharpLogRamsey.TreeShapes
end
end OAI
