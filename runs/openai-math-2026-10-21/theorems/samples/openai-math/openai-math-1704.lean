namespace OAI

noncomputable section

namespace CuntzPureness

open CuntzTrace OrderedSemigroup

open scoped TensorProduct

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]

variable (hsimple : TopologicallySimple A)

variable (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y)

lemma reducedFreeGroupAWEmbedding_value (b : ReducedFreeGroup) :
    matrixStateAWQuasitrace hsimple y hy f freeGroupScalarUltrafilter
      (reducedFreeGroupAWEmbedding hsimple y hy f b) =
        (reducedGroupTracialState (FreeGroup ℕ)).functional b :=
  (scalarTracialMatrixAWEmbedding_value hsimple y hy f freeGroupScalarUltrafilter
    (reducedFreeGroupUltraEmbedding b)).trans (reducedFreeGroupUltraEmbedding_trace b)

end CuntzPureness
end
end OAI
