noncomputable section

attribute [local instance low] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace ConnesRigidity

section

open ConnesRigidity

universe u

section ActualParabolicEmbedding

open Matrix

variable {A : Type} [CommRing A]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def rankTwoParabolicMatrix (x : ElementaryRankTwoSemidirect A) :
    Matrix (Fin 4) (Fin 4) A :=
  Matrix.reindex (finSumFinEquiv (m := 2) (n := 2))
    (finSumFinEquiv (m := 2) (n := 2))
    (Matrix.fromBlocks
      ((x.right : Matrix.SpecialLinearGroup (Fin 2) A) :
        Matrix (Fin 2) (Fin 2) A)
      (rankTwoColumnBlock (Multiplicative.toAdd x.left)) 0 1)

end ActualParabolicEmbedding
end
end ConnesRigidity
end
