namespace OAI

noncomputable section

section

open scoped BigOperators

open scoped BigOperators Matrix

open scoped Matrix

namespace CoboundaryExpanders.InfiniteChains.Join

section

open Attachment Cone

variable {V W : Type} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] [DecidableEq W] in
@[simp] lemma leftAction_single (T : Raw W →ₗ[k] Raw W)
    (s : Finset (W ⊕ V)) (a : k) :
    leftAction T (Finsupp.single s a) = prepend s.toRight (T (Finsupp.single s.toLeft a)) := by
  simp [leftAction, ← map_smul]

end
end CoboundaryExpanders.InfiniteChains.Join
end
end
end OAI
