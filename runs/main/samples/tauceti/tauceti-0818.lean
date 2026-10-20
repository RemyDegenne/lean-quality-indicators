public section

namespace TauCeti.PDCode

open Equiv Equiv.Perm

variable {n : ℕ}

open ReidemeisterThree

theorem hasReidemeisterThreeTriangle_iff (D : PDCode n) (c : Fin 3 ↪ Fin n) :
    D.HasReidemeisterThreeTriangle c ↔
      D.edgePair.val (D.crossing (c 0) 2) = D.crossing (c 1) 0 ∧
      D.edgePair.val (D.crossing (c 1) 1) = D.crossing (c 2) 3 ∧
      D.edgePair.val (D.crossing (c 0) 1) = D.crossing (c 2) 0 ∧
      (D.overPair (c 0) = D.overPair (c 2) → D.overPair (c 1) = D.overPair (c 0)) := by
  simp only [HasReidemeisterThreeTriangle, HasReidemeisterThreeTriangleArcs, and_assoc]

end TauCeti.PDCode
end
