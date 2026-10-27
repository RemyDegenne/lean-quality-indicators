public section

namespace CFSG.RankThree.PartOne.KFR4.Blk

open Module QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.OrthogonalInvolutions

section Short

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E]

variable (D : EvenNormPlane K E) (i : Fin 3)

theorem hermFourForm_projS (v : Vs K E) :
    hermFourForm D (projS D i v) = v.2.1 * v.2.2 + D.N (v.1 i) := by
  rw [projS_apply, hermFourForm_coord]

end Short
end CFSG.RankThree.PartOne.KFR4.Blk
end
